import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SecondProjectionOrthogonalComplement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

section PT

variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))

def Ip : Submodule ℤ (Vsp X.dim) where
  carrier := {x | x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨X.L.add_mem hx hy, fun a ha => ?_⟩
    rw [Hf_add_l, Complex.add_im, hx' a ha, hy' a ha, add_zero]
  zero_mem' := ⟨X.L.zero_mem, fun a _ => by simp [Hf]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨X.L.smul_mem c hx, fun a ha => ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ c x, Hf_smul_l, Complex.mul_im, hx' a ha]
    simp

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Ip {x : Vsp X.dim} : x ∈ Ip X I ↔ x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := Iff.rfl

variable {X I}

/- English proof (translation)
The claim follows from `Hf_im_span_iso (I : Set (Vsp X.dim)) hiso`.
-/
theorem iso_IR (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) :
    ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 :=
  Hf_im_span_iso (I : Set (Vsp X.dim)) hiso

/- English proof (translation)
Assemble the required witnesses or components as `⟨uc_mem _ x, fun a ha => inner_uc _ x a ha⟩`.
-/
theorem isU_uc (x : Vsp X.dim) : IsU I x (uc (IR I) x) :=
  ⟨uc_mem _ x, fun a ha => inner_uc _ x a ha⟩

/- English proof (translation)
The claim follows from `Hf_im_span_right (I : Set (Vsp X.dim)) x (fun a ha => hx.2 a ha) _ (e_mem _ k)`.
-/
theorem z_im_Ip {x : Vsp X.dim} (hx : x ∈ Ip X I) (k : Fin (dK (IR I))) : (z (IR I) k x).im = 0 :=
  Hf_im_span_right (I : Set (Vsp X.dim)) x (fun a ha => hx.2 a ha) _ (e_mem _ k)

/- English proof (translation)
Simplify using `[uc, z_im_Ip hx]`.
-/
theorem uc_Ip {x : Vsp X.dim} (hx : x ∈ Ip X I) : uc (IR I) x = 0 := by
  simp [uc, z_im_Ip hx]

/- English proof (translation)
Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `: z (IR I) k x = ((z (IR I) k x).re : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [z_im_Ip hx]`. Rewrite using `[this, Complex.coe_smul]`. Conclude with `Submodule.smul_mem _ _ (e_mem _ k)`.
-/
theorem proj_one_mem_realSpan {x : Vsp X.dim} (hx : x ∈ Ip X I) : p1 (IR I) x ∈ IR I := by
  refine Submodule.sum_mem _ fun k _ => ?_
  have : z (IR I) k x = ((z (IR I) k x).re : ℂ) := by
    apply Complex.ext <;> simp [z_im_Ip hx]
  rw [this, Complex.coe_smul]
  exact Submodule.smul_mem _ _ (e_mem _ k)

/- English proof (translation)
Simplify using `[uc, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem uc_sub (x y : Vsp X.dim) : uc (IR I) (x - y) = uc (IR I) x - uc (IR I) y := by
  simp [uc, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[uc, z, Hf_add_l, add_smul, Finset.sum_add_distrib]`.
-/
theorem uc_add (x y : Vsp X.dim) : uc (IR I) (x + y) = uc (IR I) x + uc (IR I) y := by
  simp [uc, z, Hf_add_l, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [p2, p1, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem proj_two_sub (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x - y) = p2 K x - p2 K y := by
  simp only [p2, p1, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]; abel

/- English proof (translation)
Simplify using `only [p2, p1, z, Hf_add_l, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem proj_two_add (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x + y) = p2 K x + p2 K y := by
  simp only [p2, p1, z, Hf_add_l, add_smul, Finset.sum_add_distrib]; abel

/- English proof (translation)
Establish `hK` using `iso_IR hiso`. Establish `h1 : ‖uc (IR I) v‖ ^ 2 = ∑ k, (z (IR I) k v).im ^ 2`. Rewrite using `[← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Hf_rsmul_r, Complex.im_ofReal_mul, z]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `norm_sq_decomp hK v`. Establish `h3 : ∑ k, (z (IR I) k v).im ^ 2 ≤ ∑ k, ‖z (IR I) k v‖ ^ 2` using `Finset.sum_le_sum fun k _ => by`. Rewrite using `[sq_le_sq, abs_norm]`. Conclude with `Complex.abs_im_le_norm _`.

Establish `h4 : 0 ≤ ‖p2 (IR I) v‖ ^ 2` using `sq_nonneg _`. Use polynomial arithmetic with `[norm_nonneg (uc (IR I) v), norm_nonneg v]`.
-/
theorem norm_uc_le (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (v : Vsp X.dim) :
    ‖uc (IR I) v‖ ≤ ‖v‖ := by
  have hK := iso_IR hiso
  have h1 : ‖uc (IR I) v‖ ^ 2 = ∑ k, (z (IR I) k v).im ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_rsmul_r, Complex.im_ofReal_mul, z]; ring
  have h2 := norm_sq_decomp hK v
  have h3 : ∑ k, (z (IR I) k v).im ^ 2 ≤ ∑ k, ‖z (IR I) k v‖ ^ 2 :=
    Finset.sum_le_sum fun k _ => by
      rw [sq_le_sq, abs_norm]; exact Complex.abs_im_le_norm _
  have h4 : 0 ≤ ‖p2 (IR I) v‖ ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (uc (IR I) v), norm_nonneg v]

end PT

section Split

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}

/- English proof (translation)
Establish `hf : (1 : ℝ) ≤ PT.f E`. Use `P.hfr` as an intermediate fact. Establish `: 1 ≤ PT.f E`. Break down `Nat.eq_zero_or_pos (PT.f E) with h | h` into its components or cases. Rewrite `this` using `[h]`.

Simplify using `at this`. Conclude with `h`. Conclude with `this` after adjusting the coercions. Establish `hq : (0 : ℝ) < P.q` using `by exact_mod_cast P.hq`. Establish `hRR : 0 < RR (E` using `E) := by simp only [RR]; have := P.hrd; positivity`.

Establish `hR0` using `P.hR0.1`. Simplify using `only [Par.th, th]`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises. Apply `div_pos _ hq` to reduce the goal to its premises. Establish `: 0 < P.R0 ^ 2` using `by linarith`.

Check the signs of the components of the expression.
-/
theorem th_pos (P : Par X DF) : 0 < P.th := by
  have hf : (1 : ℝ) ≤ PT.f E := by
    have := P.hfr
    have : 1 ≤ PT.f E := by
      rcases Nat.eq_zero_or_pos (PT.f E) with h | h
      · rw [h] at this; simp at this
      · exact h
    exact_mod_cast this
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  simp only [Par.th, th]
  apply Real.sqrt_pos.2
  apply div_pos _ hq
  have : 0 < P.R0 ^ 2 := by linarith
  positivity

/- English proof (translation)
Establish `hrep` using `(ob K).sum_repr ⟨a, ha⟩`. Establish `ha' : a = ∑ k, ((ob K).repr ⟨a, ha⟩ k) • e K k`. Use `congrArg Subtype.val hrep` as an intermediate fact. Simplify `this.symm` using `[e]`. Establish `hz : ∀ k, z K k a = ((ob K).repr ⟨a, ha⟩ k : ℂ)`.

Introduce `k`. Use `conv_lhs => rw [ha']`. Simplify using `only [z, Hf_sum_l, Hf_rsmul_l, Hf_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `conv_rhs => rw [ha']`. Simplify using `only [p1, hz, Complex.coe_smul]`.
-/
theorem proj_one_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p1 K a = a := by
  have hrep := (ob K).sum_repr ⟨a, ha⟩
  have ha' : a = ∑ k, ((ob K).repr ⟨a, ha⟩ k) • e K k := by
    have := congrArg Subtype.val hrep
    simpa [e] using this.symm
  have hz : ∀ k, z K k a = ((ob K).repr ⟨a, ha⟩ k : ℂ) := by
    intro k
    conv_lhs => rw [ha']
    simp only [z, Hf_sum_l, Hf_rsmul_l, Hf_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  conv_rhs => rw [ha']
  simp only [p1, hz, Complex.coe_smul]

/- English proof (translation)
Rewrite using `[p2, proj_one_of_mem hK ha, sub_self]`.
-/
theorem proj_two_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p2 K a = 0 := by
  rw [p2, proj_one_of_mem hK ha, sub_self]

variable (hI : IsSplit P I)
include hI

/- English proof (translation)
The claim follows from `iso_IR hI.iso`.
-/
theorem hK_of : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := iso_IR hI.iso

/- English proof (translation)
Establish `h` using `hI.thick x hx.1 hx.2 hxI`. Use `h.trans ?_` and prove the remaining obligations. Use `Metric.infDist_le_dist_of_mem (x := x) (proj_one_mem_realSpan hx)` as an intermediate fact. Rewrite `this` using `[dist_eq_norm]`. Simplify `this` using `[p2]`.
-/
theorem gap_le_norm_proj_two {x : Vsp X.dim} (hx : x ∈ Ip X I) (hxI : x ∉ I) : P.th ≤ ‖p2 (IR I) x‖ := by
  have h := hI.thick x hx.1 hx.2 hxI
  refine h.trans ?_
  have := Metric.infDist_le_dist_of_mem (x := x) (proj_one_mem_realSpan hx)
  rw [dist_eq_norm] at this
  simpa [p2] using this

/- English proof (translation)
Assume the negation of the conclusion as `hxI`. Establish `h1` using `gap_le_norm_proj_two hI hx hxI`. Rewrite `h1` using `[h0, norm_zero]`. Conclude with `absurd h1 (not_le.2 (th_pos P))`.
-/
theorem mem_of_proj_two_eq_zero {x : Vsp X.dim} (hx : x ∈ Ip X I) (h0 : p2 (IR I) x = 0) : x ∈ I := by
  by_contra hxI
  have h1 := gap_le_norm_proj_two hI hx hxI
  rw [h0, norm_zero] at h1
  exact absurd h1 (not_le.2 (th_pos P))

/- English proof (translation)
Rewrite using `[Hf_decomp (hK_of hI) x y, Complex.add_im, Complex.im_sum]`. Establish `: ∑ k, (z (IR I) k x * (starRingEnd ℂ) (z (IR I) k y)).im = 0` using `Finset.sum_eq_zero fun k _ => by`. Rewrite using `[Complex.mul_im, Complex.conj_re, Complex.conj_im, z_im_Ip hx, z_im_Ip hy]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, zero_add]`.
-/
theorem herm_im_proj_two {x y : Vsp X.dim} (hx : x ∈ Ip X I) (hy : y ∈ Ip X I) :
    (Hf (p2 (IR I) x) (p2 (IR I) y)).im = (Hf x y).im := by
  rw [Hf_decomp (hK_of hI) x y, Complex.add_im, Complex.im_sum]
  have : ∑ k, (z (IR I) k x * (starRingEnd ℂ) (z (IR I) k y)).im = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, z_im_Ip hx, z_im_Ip hy]; ring
  rw [this, zero_add]

/- English proof (translation)
Establish `hd : x - y ∈ Ip X I` using `(Ip X I).sub_mem hx hy`. Establish `hdI : x - y ∈ I` using `mem_of_proj_two_eq_zero hI hd (by rw [proj_two_sub, h, sub_self])`. Establish `h1` using `X.eps_add y hy.1 (x - y) (X.L.sub_mem hx.1 hy.1)`. Rewrite `h1` using `[add_sub_cancel, hI.eps _ hdI, hy.2 _ hdI]`. Simplify using `at h1`.

Conclude with `h1` after adjusting the coercions.
-/
theorem sign_eq_of_proj_two_eq {x y : Vsp X.dim} (hx : x ∈ Ip X I) (hy : y ∈ Ip X I)
    (h : p2 (IR I) x = p2 (IR I) y) : X.eps x = X.eps y := by
  have hd : x - y ∈ Ip X I := (Ip X I).sub_mem hx hy
  have hdI : x - y ∈ I := mem_of_proj_two_eq_zero hI hd (by rw [proj_two_sub, h, sub_self])
  have h1 := X.eps_add y hy.1 (x - y) (X.L.sub_mem hx.1 hy.1)
  rw [add_sub_cancel, hI.eps _ hdI, hy.2 _ hdI] at h1
  simp at h1
  exact_mod_cast h1

end Split

section Lat

/- English proof (translation)
Set `f : EuclideanSpace ℂ ι → EuclideanSpace ℝ (Fin (dK K))` to `fun u => if h : u ∈ K then (ob K).repr ⟨u, h⟩ else 0`. Establish `hf : ∀ u (h : u ∈ K), f u = (ob K).repr ⟨u, h⟩` using `fun u h => by simp [f, h]`. Establish `hinj : Set.InjOn f S`. Introduce `u hu v hv huv`. Rewrite `huv` using `[hf u (hS u hu), hf v (hS v hv)]`.

Conclude with `congrArg Subtype.val ((ob K).repr.injective huv)`. Establish `hcard` using `Finset.card_image_of_injOn hinj`. Rewrite using `[← hcard]`. Apply `hP (dK K) (S.image f) δ R hδ hδR` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨u, hu, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[hf u (hS u hu), LinearIsometryEquiv.norm_map]`. Conclude with `hR u hu`. Introduce `x hx y hy hxy`. Take `⟨u, hu, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hy`. Establish `huv : u ≠ v` using `fun h => hxy (by rw [h])`. Rewrite using `[hf u (hS u hu), hf v (hS v hv), LinearIsometryEquiv.dist_map]`. Conclude with `hsep u hu v hv huv`.
-/
theorem pack_K {ι : Type} [Fintype ι] (hP : Ext.PackingCount) (K : Submodule ℝ (EuclideanSpace ℂ ι))
    (S : Finset (EuclideanSpace ℂ ι)) (hS : ∀ u ∈ S, u ∈ K) (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hR : ∀ u ∈ S, ‖u‖ ≤ R) (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → δ ≤ dist u v) :
    (S.card : ℝ) ≤ (3 * R / δ) ^ (dK K) := by
  classical
  let f : EuclideanSpace ℂ ι → EuclideanSpace ℝ (Fin (dK K)) :=
    fun u => if h : u ∈ K then (ob K).repr ⟨u, h⟩ else 0
  have hf : ∀ u (h : u ∈ K), f u = (ob K).repr ⟨u, h⟩ := fun u h => by simp [f, h]
  have hinj : Set.InjOn f S := by
    intro u hu v hv huv
    rw [hf u (hS u hu), hf v (hS v hv)] at huv
    exact congrArg Subtype.val ((ob K).repr.injective huv)
  have hcard := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hP (dK K) (S.image f) δ R hδ hδR
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    rw [hf u (hS u hu), LinearIsometryEquiv.norm_map]
    exact hR u hu
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    have huv : u ≠ v := fun h => hxy (by rw [h])
    rw [hf u (hS u hu), hf v (hS v hv), LinearIsometryEquiv.dist_map]
    exact hsep u hu v hv huv

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}

/- English proof (translation)
Establish `hq : (0 : ℝ) < P.q` using `by exact_mod_cast P.hq`. Establish `hRR : 0 < RR (E` using `E) := by simp only [RR]; have := P.hrd; positivity`. Establish `hR0` using `P.hR0.1`. Establish `: 0 < P.R0 ^ 2` using `by linarith`. Simplify using `only [b0]`.

Check the signs of the components of the expression.
-/
theorem cutoff_pos (P : Par X DF) : 0 < b0 (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  have : 0 < P.R0 ^ 2 := by linarith
  simp only [b0]; positivity

variable (hI : IsSplit P I)
include hI

/- English proof (translation)
Rewrite using `[dist_eq_norm, ← uc_sub]`. Establish `hu` using `isU_uc (I := I) (y - y')`. Establish `h0 : uc (IR I) (y - y') ≠ 0` using `by rw [uc_sub]; exact sub_ne_zero.2 hne`. Use `hI.sep _ (X.L.sub_mem hy hy') _ hu h0` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uc_sep {y y' : Vsp X.dim} (hy : y ∈ X.L) (hy' : y' ∈ X.L)
    (hne : uc (IR I) y ≠ uc (IR I) y') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uc (IR I) y) (uc (IR I) y') := by
  rw [dist_eq_norm, ← uc_sub]
  have hu := isU_uc (I := I) (y - y')
  have h0 : uc (IR I) (y - y') ≠ 0 := by rw [uc_sub]; exact sub_ne_zero.2 hne
  have := hI.sep _ (X.L.sub_mem hy hy') _ hu h0
  calc Real.sqrt (b0 (E := E) P.q P.R0) ≤ Real.sqrt (‖uc (IR I) (y - y')‖ ^ 2) := Real.sqrt_le_sqrt this
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/- English proof (translation)
Use `set F : Set (Vsp X.dim) := {u | ∃ y ∈ X.L, ‖uc (IR I) y‖ ≤ C ∧ uc (IR I) y = u} with hF`. Establish `hb` using `cutoff_pos P`. Use `set δ := Real.sqrt (b0 (E := E) P.q P.R0)`. Establish `hδ : 0 < δ` using `Real.sqrt_pos.2 hb`. Establish `hfin : F.Finite`.

Assume the negation of the conclusion as `hinf`. Use `set R := max C δ`. Take `⟨N, hN⟩` from `exists_nat_gt ((3 * R / δ) ^ (dK (IR I)))`. Take `⟨T, hTF, hTc⟩` from `Set.Infinite.exists_subset_card_eq hinf N`. Use `pack_K hP (IR I) T (fun u hu => by` as an intermediate fact.

Take `⟨y, -, -, rfl⟩` from `hTF hu`. Conclude with `uc_mem _ y) δ R hδ (le_max_right _ _)`. Use the proof step `(fun u hu => by obtain ⟨y, -, hyC, rfl⟩ := hTF hu; exact hyC.trans (le_max_left _ _))`. Use the proof step `(fun u hu v hv huv => by`. Take `⟨y, hy, -, rfl⟩` from `hTF hu`.

Take `⟨y', hy', -, rfl⟩` from `hTF hv`. Conclude with `uc_sep hI hy hy' huv)`. Rewrite `this` using `[hTc]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `g : Vsp X.dim → Vsp X.dim` to `fun u => if h : u ∈ F then Classical.choose h else 0`.

Establish `hg : ∀ u ∈ F, g u ∈ X.L ∧ uc (IR I) (g u) = u`. Introduce `u hu`. Use `Classical.choose_spec hu` as an intermediate fact. Simplify using `only [g, dif_pos hu]`. Conclude with `⟨this.1, this.2.2⟩`.

Use `⟨∑ u ∈ hfin.toFinset, ‖p2 (IR I) (g u)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y hy hyC => ?_⟩` and prove the remaining obligations. Establish `hu : uc (IR I) y ∈ F` using `⟨y, hy, hyC, rfl⟩`. Use `⟨g (uc (IR I) y), (hg _ hu).1, (hg _ hu).2, ?_⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun u => ‖p2 (IR I) (g u)‖) (fun _ _ => norm_nonneg _) (hfin.mem_toFinset.2 hu)`.
-/
theorem reps_bdd (hP : Ext.PackingCount) (C : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ X.L, ‖uc (IR I) y‖ ≤ C →
      ∃ y' ∈ X.L, uc (IR I) y' = uc (IR I) y ∧ ‖p2 (IR I) y'‖ ≤ M := by
  classical
  set F : Set (Vsp X.dim) := {u | ∃ y ∈ X.L, ‖uc (IR I) y‖ ≤ C ∧ uc (IR I) y = u} with hF
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  have hfin : F.Finite := by
    by_contra hinf
    set R := max C δ
    obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R / δ) ^ (dK (IR I)))
    obtain ⟨T, hTF, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have := pack_K hP (IR I) T (fun u hu => by
        obtain ⟨y, -, -, rfl⟩ := hTF hu; exact uc_mem _ y) δ R hδ (le_max_right _ _)
      (fun u hu => by obtain ⟨y, -, hyC, rfl⟩ := hTF hu; exact hyC.trans (le_max_left _ _))
      (fun u hu v hv huv => by
        obtain ⟨y, hy, -, rfl⟩ := hTF hu
        obtain ⟨y', hy', -, rfl⟩ := hTF hv
        exact uc_sep hI hy hy' huv)
    rw [hTc] at this
    linarith
  let g : Vsp X.dim → Vsp X.dim := fun u => if h : u ∈ F then Classical.choose h else 0
  have hg : ∀ u ∈ F, g u ∈ X.L ∧ uc (IR I) (g u) = u := by
    intro u hu
    have := Classical.choose_spec hu
    simp only [g, dif_pos hu]
    exact ⟨this.1, this.2.2⟩
  refine ⟨∑ u ∈ hfin.toFinset, ‖p2 (IR I) (g u)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    fun y hy hyC => ?_⟩
  have hu : uc (IR I) y ∈ F := ⟨y, hy, hyC, rfl⟩
  refine ⟨g (uc (IR I) y), (hg _ hu).1, (hg _ hu).2, ?_⟩
  exact Finset.single_le_sum (f := fun u => ‖p2 (IR I) (g u)‖) (fun _ _ => norm_nonneg _)
    (hfin.mem_toFinset.2 hu)

end Lat

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
