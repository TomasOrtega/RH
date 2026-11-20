import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticConstant
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.Residue
import GroundTheory.GlobalFields.ComplexMultiplication.ResidueTheorem
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticResidues

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

variable (L) in

def torusOrder (f : ℂ → ℂ) (x : Torus L) : ℤ :=
  (meromorphicOrderAt f x.out).untopD 0

/- English proof (translation)
Establish `h` using `(Torus.mk_eq_mk_iff L).1 (QuotientAddGroup.out_eq' (Torus.mk L z))`. Use `hf.2.meromorphicOrderAt_add h z` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[torusOrder, this]`.
-/
lemma torusOrder_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusOrder L f (Torus.mk L z) = (meromorphicOrderAt f z).untopD 0 := by
  have h := (Torus.mk_eq_mk_iff L).1 (QuotientAddGroup.out_eq' (Torus.mk L z))
  have := hf.2.meromorphicOrderAt_add h z
  rw [add_sub_cancel] at this
  rw [torusOrder, this]

/- English proof (translation)
Use `⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩` and prove the remaining obligations. Establish `: logDeriv f = fun w ↦ deriv f w / f w` using `rfl`. Rewrite using `[this]`. Conclude with `(hf.1 z).deriv.div (hf.1 z)`. Simplify using `only [logDeriv_apply]`.

Rewrite using `[hf.2 z l hl]`. Use `congr 1`. Rewrite using `[← deriv_comp_add_const, hf.2.comp_add hl]`.
-/
lemma isEllipticFunction_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    IsEllipticFunction L (logDeriv f) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩
  · have : logDeriv f = fun w ↦ deriv f w / f w := rfl
    rw [this]
    exact (hf.1 z).deriv.div (hf.1 z)
  · simp only [logDeriv_apply]
    rw [hf.2 z l hl]
    congr 1
    rw [← deriv_comp_add_const, hf.2.comp_add hl]

/- English proof (translation)
Distinguish the cases in `htop : meromorphicOrderAt f z = ⊤`. Rewrite using `[htop, WithTop.untopD_top, Int.cast_zero]`. Rewrite `htop` using `[meromorphicOrderAt_eq_top_iff]`. Establish `hmer : MeromorphicAt (logDeriv f) z`. Establish `: logDeriv f = fun w ↦ deriv f w / f w` using `rfl`.

Rewrite using `[this]`. Conclude with `hf.deriv.div hf`. Establish `h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ)` using `by filter_upwards [htop] with w hw`. Simplify using `[logDeriv_apply, hw]`. Rewrite using `[residue_congr hmer h0]`.

Conclude with `residue_eq_zero_of_analyticAt analyticAt_const`. Take `⟨n, hn⟩` from `WithTop.ne_top_iff_exists.1 htop`. Rewrite using `[← hn, WithTop.untopD_coe]`. Conclude with `residue_logDeriv hf hn.symm`.
-/
lemma residue_logDeriv_eq_untopD {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · rw [htop, WithTop.untopD_top, Int.cast_zero]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hmer : MeromorphicAt (logDeriv f) z := by
      have : logDeriv f = fun w ↦ deriv f w / f w := rfl
      rw [this]
      exact hf.deriv.div hf
    have h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [htop] with w hw
      simp [logDeriv_apply, hw]
    rw [residue_congr hmer h0]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hn, WithTop.untopD_coe]
    exact residue_logDeriv hf hn.symm

/- English proof (translation)
The claim follows from `residue_logDeriv_eq_untopD (hf.1 _)`.
-/
lemma torusResidue_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (x : Torus L) :
    torusResidue L (logDeriv f) x = (torusOrder L f x : ℂ) :=
  residue_logDeriv_eq_untopD (hf.1 _)

/- English proof (translation)
Use `(finite_image_singularSet L hf.1 hf.2).subset ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩` and prove the remaining obligations.
-/
lemma finite_support_torusResidue {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by
  refine (finite_image_singularSet L hf.1 hf.2).subset ?_
  intro x hx
  refine ⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩

/- English proof (translation)
Use `(finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢`. Conclude with `hx` after adjusting the coercions.
-/
lemma finite_support_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusOrder L f)).Finite := by
  refine (finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_
  intro x hx
  simp only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢
  exact_mod_cast hx

/- English proof (translation)
Establish `h` using `finsum_torusResidue_eq_zero (isEllipticFunction_logDeriv hf)`. Rewrite `h` using `[torusResidue_logDeriv hf]`. Establish `hc` using `(Int.castAddHom ℂ).map_finsum (finite_support_torusOrder hf)`. Simplify using `only [Int.coe_castAddHom] at hc`. Rewrite `h` using `[← hc]`.

Conclude with `h` after adjusting the coercions.
-/
theorem finsum_torusOrder_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusOrder L f x = 0 := by
  have h := finsum_torusResidue_eq_zero (isEllipticFunction_logDeriv hf)
  simp_rw [torusResidue_logDeriv hf] at h
  have hc := (Int.castAddHom ℂ).map_finsum (finite_support_torusOrder hf)
  simp only [Int.coe_castAddHom] at hc
  rw [← hc] at h
  exact_mod_cast h

variable (L) in

def degree (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ x : Torus L, (-torusOrder L f x).toNat

/- English proof (translation)
Establish `hc : MeromorphicAt (fun _ : ℂ ↦ -c) z` using `analyticAt_const.meromorphicAt`. Establish `e : (fun w ↦ f w - c) = f + fun _ ↦ -c`. Use function extensionality and compare the values at `w`. Simplify using `[sub_eq_add_neg]`. Establish `hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z` using `analyticAt_const.meromorphicOrderAt_nonneg`.

Rewrite using `[e]`. Distinguish the cases in `hneg : meromorphicOrderAt f z < 0`. Rewrite using `[meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]`. Use `push Not at hneg`. Establish `h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z` using `le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)`.

Establish `key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0`. Introduce `o ho`. Proceed by induction on `o with`. Consider the case `top => simp`. Consider the case `coe n`.

Simplify using `only [WithTop.untopD_coe]`. Establish `: (0 : ℤ) ≤ n` using `by exact_mod_cast ho`. Use linear arithmetic over natural numbers and integers. Rewrite using `[key _ h1, key _ hneg]`.
-/
lemma toNat_neg_untopD_sub_const {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) :
    (-(meromorphicOrderAt (fun w ↦ f w - c) z).untopD 0).toNat =
      (-(meromorphicOrderAt f z).untopD 0).toNat := by
  have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
  have e : (fun w ↦ f w - c) = f + fun _ ↦ -c := by
    funext w; simp [sub_eq_add_neg]
  have hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicOrderAt_nonneg
  rw [e]
  by_cases hneg : meromorphicOrderAt f z < 0
  · rw [meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]
  · push Not at hneg
    have h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z :=
      le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)
    have key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0 := by
      intro o ho
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (0 : ℤ) ≤ n := by exact_mod_cast ho
        omega
    rw [key _ h1, key _ hneg]

/- English proof (translation)
Proceed by induction on `o with`. Consider the case `top => exact le_top`. Consider the case `coe n`. Simplify using `only [WithTop.untopD_coe] at h`. Conclude with `(by omega : (0 : ℤ) ≤ n)` after adjusting the coercions.
-/
lemma nonneg_of_toNat_neg_untopD_eq_zero {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 0) :
    0 ≤ o := by
  induction o with
  | top => exact le_top
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

/- English proof (translation)
Proceed by induction on `o with`. Consider the case `top => simp`. Consider the case `coe n`. Simplify using `only [WithTop.untopD_coe]`. Establish `: (0 : ℤ) ≤ n` using `by exact_mod_cast h`.

Use linear arithmetic over natural numbers and integers.
-/
lemma toNat_neg_untopD_eq_zero_of_nonneg {o : WithTop ℤ} (h : 0 ≤ o) :
    (-(o.untopD 0)).toNat = 0 := by
  induction o with
  | top => simp
  | coe n =>
    simp only [WithTop.untopD_coe]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    omega

/- English proof (translation)
Proceed by induction on `o with`. Consider the case `top => simp at h`. Consider the case `coe n`. Simplify using `only [WithTop.untopD_coe] at h`. Establish `: n = -1` using `by omega`.

Rewrite using `[this]`.
-/
lemma eq_neg_one_of_toNat_neg_untopD_eq_one {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 1) :
    o = ((-1 : ℤ) : WithTop ℤ) := by
  induction o with
  | top => simp at h
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    have : n = -1 := by omega
    rw [this]

/- English proof (translation)
Rewrite `h` using `[Filter.Eventually, codiscrete, mem_codiscreteWithin]`. Use `disjoint_principal_right.1 (h x (mem_univ x))` as an intermediate fact. Use `filter_upwards [this] with z hz`. Assume the negation of the conclusion as `hpz`. Conclude with `hz ⟨mem_univ z, hpz⟩`.
-/
lemma eventually_nhdsNE_of_eventually_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  rw [Filter.Eventually, codiscrete, mem_codiscreteWithin] at h
  have := disjoint_principal_right.1 (h x (mem_univ x))
  filter_upwards [this] with z hz
  by_contra hpz
  exact hz ⟨mem_univ z, hpz⟩

/- English proof (translation)
The claim follows from `(finite_support_torusOrder hf).subset fun x hx ↦ by simp only [Function.mem_support] at hx ⊢ omega`.
-/
lemma finite_support_toNat_neg_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support fun x ↦ (-torusOrder L f x).toNat).Finite :=
  (finite_support_torusOrder hf).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

/- English proof (translation)
Establish `hg : IsEllipticFunction L (fun z ↦ f z - c)`. Use `⟨fun z ↦ ?_, fun z l hl ↦ by simp only [hf.2 z l hl]⟩` and prove the remaining obligations. Use `hf.1 z` as an intermediate fact. Use `fun_prop`. Use `set g : ℂ → ℂ := fun z ↦ f z - c with hgdef`.

Establish `hfin` using `finite_support_torusOrder hg`. Use `set s := hfin.toFinset with hs`. Establish `hsupp : Function.support (torusOrder L g) ⊆ ↑s` using `by simp [hs]`. Establish `hsum` using `finsum_torusOrder_eq_zero hg`. Rewrite `hsum` using `[finsum_eq_sum_of_support_subset _ hsupp]`.

Establish `h1 : ∑ᶠ x, (torusOrder L g x).toNat = ∑ x ∈ s, (torusOrder L g x).toNat` using `finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by`. Simplify using `only [Function.mem_support] at hx ⊢`. Use the proof step `omega)`. Establish `hpt : ∀ x, (-torusOrder L f x).toNat = (-torusOrder L g x).toNat` using `fun x ↦ (toNat_neg_untopD_sub_const (hf.1 _) c).symm`. Establish `h2 : degree L f = ∑ x ∈ s, (-torusOrder L g x).toNat`.

Rewrite using `[degree]`. Repeatedly rewrite using `[hpt]`. Conclude with `finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by`. Simplify using `only [Function.mem_support] at hx ⊢`. Use the proof step `omega)`.

Rewrite using `[h1, h2]`. Establish `key : ∀ x, ((torusOrder L g x).toNat : ℤ) - ((-torusOrder L g x).toNat : ℤ) = torusOrder L g x` using `fun x ↦ Int.toNat_sub_toNat_neg _`. Establish `: ((∑ x ∈ s, (torusOrder L g x).toNat : ℕ) : ℤ) = ((∑ x ∈ s, (-torusOrder L g x).toNat : ℕ) : ℤ)`. Use `push_cast`. Rewrite using `[← sub_eq_zero, ← Finset.sum_sub_distrib]`.

Simplify using `only [key]`. Conclude with `hsum`. Conclude with `this` after adjusting the coercions.
-/
theorem finsum_toNat_torusOrder_sub_const {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun z ↦ f z - c) x).toNat = degree L f := by
  classical
  have hg : IsEllipticFunction L (fun z ↦ f z - c) := by
    refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [hf.2 z l hl]⟩
    have := hf.1 z
    fun_prop
  set g : ℂ → ℂ := fun z ↦ f z - c with hgdef
  have hfin := finite_support_torusOrder hg
  set s := hfin.toFinset with hs
  have hsupp : Function.support (torusOrder L g) ⊆ ↑s := by simp [hs]
  have hsum := finsum_torusOrder_eq_zero hg
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
  have h1 : ∑ᶠ x, (torusOrder L g x).toNat = ∑ x ∈ s, (torusOrder L g x).toNat :=
    finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  have hpt : ∀ x, (-torusOrder L f x).toNat = (-torusOrder L g x).toNat := fun x ↦
    (toNat_neg_untopD_sub_const (hf.1 _) c).symm
  have h2 : degree L f = ∑ x ∈ s, (-torusOrder L g x).toNat := by
    rw [degree]
    simp_rw [hpt]
    exact finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  rw [h1, h2]
  have key : ∀ x, ((torusOrder L g x).toNat : ℤ) - ((-torusOrder L g x).toNat : ℤ) =
      torusOrder L g x := fun x ↦ Int.toNat_sub_toNat_neg _
  have : ((∑ x ∈ s, (torusOrder L g x).toNat : ℕ) : ℤ) =
      ((∑ x ∈ s, (-torusOrder L g x).toNat : ℕ) : ℤ) := by
    push_cast
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [key]
    exact hsum
  exact_mod_cast this

/- English proof (translation)
Simplify using `using finsum_toNat_torusOrder_sub_const hf 0`.
-/
theorem finsum_toNat_torusOrder_eq_degree {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, (torusOrder L f x).toNat = degree L f := by
  simpa using finsum_toNat_torusOrder_sub_const hf 0

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Rewrite `h` using `[finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)]`. Conclude with `hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))`.
-/
lemma eq_zero_of_finsum_eq_zero_nat {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (h : ∑ᶠ x, u x = 0) (x : α) : u x = 0 := by
  classical
  by_contra hx
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)] at h
  exact hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `hall` using `eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0`. Apply `exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hf.1 hf.2` to reduce the goal to its premises. Introduce `z`.

Use `hall (Torus.mk L z)` as an intermediate fact. Rewrite `this` using `[torusOrder_mk hf]`. Conclude with `nonneg_of_toNat_neg_untopD_eq_zero this`. Introduce and unpack `⟨c, hc⟩`. Rewrite using `[degree]`.

Establish `: ∀ x : Torus L, (-torusOrder L f x).toNat = 0`. Introduce `x`. Apply `toNat_neg_untopD_eq_zero_of_nonneg` to reduce the goal to its premises. Rewrite using `[meromorphicOrderAt_congr (eventually_nhdsNE_of_eventually_codiscrete hc x.out)]`. Conclude with `analyticAt_const.meromorphicOrderAt_nonneg`.

Simplify using `[this]`.
-/
theorem degree_eq_zero_iff {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    degree L f = 0 ↔ ∃ c : ℂ, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  constructor
  · intro h0
    have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    apply exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hf.1 hf.2
    intro z
    have := hall (Torus.mk L z)
    rw [torusOrder_mk hf] at this
    exact nonneg_of_toNat_neg_untopD_eq_zero this
  · rintro ⟨c, hc⟩
    rw [degree]
    have : ∀ x : Torus L, (-torusOrder L f x).toNat = 0 := by
      intro x
      apply toNat_neg_untopD_eq_zero_of_nonneg
      rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_eventually_codiscrete hc x.out)]
      exact analyticAt_const.meromorphicOrderAt_nonneg
    simp [this]

/- English proof (translation)
Introduce `h1`. Use `set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu`. Establish `hfin : (Function.support u).Finite` using `finite_support_toNat_neg_torusOrder hf`. Use `set s := hfin.toFinset with hs`. Establish `hsum : ∑ x ∈ s, u x = 1`.

Rewrite using `[← finsum_eq_sum_of_support_subset u (by simp [hs])]`. Conclude with `h1`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Rewrite `hsum` using `[Finset.sum_eq_zero hcon]`. Conclude with `zero_ne_one hsum`. Establish `hsplit` using `Finset.add_sum_erase s u hx₀s`. Rewrite `hsplit` using `[hsum]`. Establish `hux₀ : u x₀ = 1` using `by omega`.

Establish `hrest : ∀ x, x ≠ x₀ → u x = 0`. Introduce `x hx`. Distinguish the cases in `hxs : x ∈ s`. Establish `h0 : ∑ y ∈ s.erase x₀, u y = 0` using `by omega`. Conclude with `Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)`.

Simplify `hxs` using `[hs]`. Establish `hres` using `finsum_torusResidue_eq_zero hf`. Rewrite `hres` using `[finsum_eq_single _ x₀ (fun x hx ↦ ?_)]`. Establish `hord` using `eq_neg_one_of_toNat_neg_untopD_eq_one hux₀`. Conclude with `residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres`.

Conclude with `residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _) (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))`.
-/
theorem degree_ne_one {f : ℂ → ℂ} (hf : IsEllipticFunction L f) : degree L f ≠ 1 := by
  classical
  intro h1
  set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu
  have hfin : (Function.support u).Finite := finite_support_toNat_neg_torusOrder hf
  set s := hfin.toFinset with hs
  have hsum : ∑ x ∈ s, u x = 1 := by
    rw [← finsum_eq_sum_of_support_subset u (by simp [hs])]
    exact h1
  obtain ⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact zero_ne_one hsum
  have hsplit := Finset.add_sum_erase s u hx₀s
  rw [hsum] at hsplit
  have hux₀ : u x₀ = 1 := by omega
  have hrest : ∀ x, x ≠ x₀ → u x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · have h0 : ∑ y ∈ s.erase x₀, u y = 0 := by omega
      exact Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)
    · simpa [hs] using hxs
  have hres := finsum_torusResidue_eq_zero hf
  rw [finsum_eq_single _ x₀ (fun x hx ↦ ?_)] at hres
  · have hord := eq_neg_one_of_toNat_neg_untopD_eq_one hux₀
    exact residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres
  · exact residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _)
      (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))

/- English proof (translation)
Establish `hP : IsEllipticFunction L ℘[L]` using `isEllipticFunction_weierstrassP`. Establish `h0 : (0 : Torus L) = Torus.mk L 0` using `(QuotientAddGroup.mk_zero _).symm`. Rewrite using `[degree, finsum_eq_single _ (0 : Torus L) ?_]`. Rewrite using `[h0, torusOrder_mk hP]`. Establish `h2 : meromorphicOrderAt ℘[L] 0 = ((-2 : ℤ) : WithTop ℤ)`.

Rewrite using `[L.order_weierstrassP 0 (zero_mem _)]`. Evaluate the numerical expressions. Rewrite using `[h2, WithTop.untopD_coe]`. Both sides reduce to the same expression. Introduce `x hx`.

Take `⟨z, rfl⟩` from `Torus.mk_surjective L x`. Establish `hz : z ∉ L.lattice` using `fun h ↦ hx (by`. Rewrite using `[h0]`. Conclude with `(Torus.mk_eq_mk_iff L).2 (by simpa using h))`. Rewrite using `[torusOrder_mk hP]`.

Conclude with `toNat_neg_untopD_eq_zero_of_nonneg (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg`.
-/
theorem degree_weierstrassP : degree L ℘[L] = 2 := by
  have hP : IsEllipticFunction L ℘[L] := isEllipticFunction_weierstrassP
  have h0 : (0 : Torus L) = Torus.mk L 0 := (QuotientAddGroup.mk_zero _).symm
  rw [degree, finsum_eq_single _ (0 : Torus L) ?_]
  · rw [h0, torusOrder_mk hP]
    have h2 : meromorphicOrderAt ℘[L] 0 = ((-2 : ℤ) : WithTop ℤ) := by
      rw [L.order_weierstrassP 0 (zero_mem _)]
      norm_num
    rw [h2, WithTop.untopD_coe]
    rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    have hz : z ∉ L.lattice := fun h ↦ hx (by
      rw [h0]
      exact (Torus.mk_eq_mk_iff L).2 (by simpa using h))
    rw [torusOrder_mk hP]
    exact toNat_neg_untopD_eq_zero_of_nonneg
      (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg

end Elliptic
end GroundTheory.Global
