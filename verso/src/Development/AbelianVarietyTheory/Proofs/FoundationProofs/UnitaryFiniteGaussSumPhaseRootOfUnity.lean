import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSum
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussPhase

/- English proof (translation)
Establish `h1 : Finite (G ⧸ P.toIntSubmodule)` using `(inferInstance : Finite (G ⧸ P))`. Establish `h2` using `(Submodule.finiteQuotient_iff _).1 h1`. Set `ψ : P.toIntSubmodule →ₗ[ℤ] G` to `φ.toIntLinearMap`. Establish `h3 : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ G`. Establish `hψ : Function.Injective ψ` using `fun x y h => hφ h`.

Conclude with `(LinearMap.finrank_range_of_inj hψ).trans h2`. Establish `h4 : Finite (G ⧸ (LinearMap.range ψ).toAddSubgroup)` using `Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range ψ) h3`. Establish `h5 : (LinearMap.range ψ).toAddSubgroup = φ.range`. Use extensionality with `x`. Conclude with `⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩`.

Rewrite `h4` using `[h5]`. Then use the resulting hypothesis.
-/
theorem finite_quot {G : Type} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] (P : AddSubgroup G)
    [P.FiniteIndex] (φ : P →+ G) (hφ : Function.Injective φ) : Finite (G ⧸ φ.range) := by
  have h1 : Finite (G ⧸ P.toIntSubmodule) := (inferInstance : Finite (G ⧸ P))
  have h2 := (Submodule.finiteQuotient_iff _).1 h1
  let ψ : P.toIntSubmodule →ₗ[ℤ] G := φ.toIntLinearMap
  have h3 : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ G := by
    have hψ : Function.Injective ψ := fun x y h => hφ h
    exact (LinearMap.finrank_range_of_inj hψ).trans h2
  have h4 : Finite (G ⧸ (LinearMap.range ψ).toAddSubgroup) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range ψ) h3
  have h5 : (LinearMap.range ψ).toAddSubgroup = φ.range := by
    ext x; exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  rwa [h5] at h4

noncomputable def ex (t : ℝ) : ℂ := cexp (-((π : ℂ) * I) * (t : ℂ))

/- English proof (translation)
Simplify using `only [ex, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

/- English proof (translation)
Simplify using `[ex]`.
-/
theorem ex_zero : ex 0 = 1 := by simp [ex]

/- English proof (translation)
Rewrite using `[ex, ← Complex.exp_int_mul_two_pi_mul_I (-m)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_two (m : ℤ) : ex (2 * m) = 1 := by
  rw [ex, ← Complex.exp_int_mul_two_pi_mul_I (-m)]; congr 1; push_cast; ring

/- English proof (translation)
Simplify using `only [ex, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_pow (t : ℝ) (k : ℕ) : ex t ^ k = ex (k * t) := by
  simp only [ex, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

/- English proof (translation)
Introduce `V _ _ H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa`. Take `⟨hα1, hint, hadd⟩` from `hα`. Establish `hanti : ∀ x y, (H x y).im = -(H y x).im` using `fun x y => by rw [hH.1 x y]; simp`. Establish `hself : ∀ x, (H x x).im = 0` using `fun x => by have := hanti x x; linarith`. Establish `hadj : ∀ x y, (H (B x) y).im - (H (B y) x).im = (H x y).im`.

Introduce `x y`. Establish `h1 : H (B x) y + H x (B y) = H x y`. Establish `hx` using `hB1 x`. Establish `hy` using `hB1 y`. Generalize the expression as in `B x = u at hx ⊢`.

Generalize the expression as in `B y = v at hy ⊢`. Substitute `hx hy` using the available equality. Simplify using `only [map_sub, LinearMap.sub_apply, ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `congrArg Complex.im h1`.

Rewrite `h2` using `[Complex.add_im, hanti x (B y)]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `ph : V → ℂ` to `fun x => α x * ex (H (B x) x).im`. Establish `hadd' : ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * ex (H x y).im` using `hadd`. Apply the tactic sequence `have hsq : ∀ x ∈ Λ, α x ^ 2 = 1 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]`.

Apply the tactic sequence `have hne : ∀ x ∈ Λ, α x ≠ 0 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]`. Establish `hα0 : α 0 = 1`. Use `hadd' 0 Λ.zero_mem 0 Λ.zero_mem` as an intermediate fact. Rewrite `this` using `[add_zero, hself, ex_zero, mul_one]`. Conclude with `(mul_eq_left₀ (hne 0 Λ.zero_mem)).1 this.symm`.

Establish `hph0 : ph 0 = 1` using `by simp [ph, hα0, ex_zero]`. Establish `hph : ∀ x ∈ Λ, ∀ y ∈ Λ, ph (x + y) = ph x * ph y * ex (2 * (H (B x) y).im)`. Introduce `x hx y hy`. Establish `e : (H (B (x + y)) (x + y)).im + (H x y).im = (H (B x) x).im + (H (B y) y).im + 2 * (H (B x) y).im`. Simplify using `only [map_add, LinearMap.add_apply, Complex.add_im, ← hadj x y]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e'` using `congrArg ex e`. Rewrite `e'` using `[ex_add, ex_add, ex_add]`. Simplify using `only [ph, hadd' x hx y hy]`. Take the linear combination `α x * α y * e'`.

Establish `hmem : ∀ y ∈ Λ', y - a y ∈ Λ` using `fun y hy => Λ.sub_mem (hle hy) (haΛ y hy)`. Establish `hphA : ∀ y ∈ Λ', ph (y - a y) = 1`. Introduce `y hy`. Establish `h` using `hadd' _ (hmem y hy) _ (haΛ y hy)`. Rewrite `h` using `[sub_add_cancel, hαa y hy]`.

Establish `h' : α (y - a y) * ex (H (y - a y) (a y)).im = 1` using `(mul_eq_left₀ (hne y (hle hy))).1 (by linear_combination -h)`. Take `⟨m, hm⟩` from `hint y (hle hy) (a y) (haΛ y hy)`. Establish `e1 : (H (y - a y) (a y)).im = m`. Simplify using `only [map_sub, LinearMap.sub_apply, Complex.sub_im, hself, hm, sub_zero]`. Establish `e2 : (H (B (y - a y)) (y - a y)).im = m + 2 * ((-m : ℤ) : ℝ)`.

Rewrite using `[hB2]`. Simplify using `only [map_sub, Complex.sub_im, hself, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ph]`.

Rewrite using `[e2, ex_add, ex_two, mul_one, ← e1, h']`. Establish `hper : ∀ x ∈ Λ, ∀ y ∈ Λ', ph (y - a y + x) = ph x`. Introduce `x hx y hy`. Take `⟨m, hm⟩` from `hint y (hle hy) x hx`. Rewrite using `[hph _ (hmem y hy) x hx, hphA y hy, hB2, hm, ex_two, one_mul, mul_one]`.

Set `φ : Λ'.addSubgroupOf Λ →+ Λ` to `AddMonoidHom.mk' (fun y => ⟨((y : Λ) : V) - a ((y : Λ) : V), hmem _ y.2⟩) (fun y z => Subtype.ext (by simp only [AddSubgroup.coe_add, map_add]; abel))`. Establish `hφ : ∀ y, ((φ y : Λ) : V) = ((y : Λ) : V) - a ((y : Λ) : V)` using `fun _ => rfl`. Establish `hinj : Function.Injective φ`. Introduce `y z h`. Use `congrArg (fun t : Λ => B (t : V)) h` as an intermediate fact.

Simplify using `only [hφ, hB2] at this`. Conclude with `Subtype.ext (Subtype.ext this)`. Establish `: Module.Finite ℤ Λ` using `Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)`. Establish `: IsAddTorsionFree V` using `.of_isTorsionFree ℂ V`. Establish `: Module.Free ℤ Λ` using `inferInstance`.

Use `finite_quot _ φ hinj` as an intermediate fact. Set `_ : Fintype (Λ ⧸ φ.range)` to `Fintype.ofFinite _`. Establish `hrel : ∀ x x' : Λ, (x : Λ ⧸ φ.range) = x' ↔ ∃ y ∈ Λ', (x' : V) = y - a y + x`. Introduce `x x'`. Rewrite using `[QuotientAddGroup.eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨_, y.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hy` as an intermediate fact. Rewrite `this` using `[hφ]`.

Use `erw [this]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨y, hy, h⟩`. Use `⟨⟨⟨y, hle hy⟩, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`.

Simplify using `[h]`. Establish `hf : ∀ x : Λ, ph ((Quotient.out (x : Λ ⧸ φ.range) : Λ) : V) = ph x`. Introduce `x`. Take `⟨y, hy, h⟩` from `(hrel x _).1 (QuotientAddGroup.out_eq' _).symm`. Rewrite using `[h, hper _ x.2 y hy]`.

Use `⟨Λ ⧸ φ.range, inferInstance, fun m => ((Quotient.out m : Λ) : V), fun m => (Quotient.out m).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, h⟩` from `(hrel ⟨x, hx⟩ _).1 (QuotientAddGroup.out_eq' _).symm`. Use `⟨(((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range), ⟨y, hy⟩), by simp only [h]; abel, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨m, z, hz⟩ h'`.

Simplify using `only at h'`. Establish `hm : ((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range) = m`. Rewrite using `[← QuotientAddGroup.out_eq' m, hrel]`. Conclude with `⟨z, hz, by simp only [h']; abel⟩`. Substitute `hm` using the available equality.

Use `Prod.ext rfl (Subtype.ext ?_)` and prove the remaining obligations. Rewrite `h'` using `[h]`. Establish `: z - a z = y - a y`. Establish `h'' : x = y - a y + x - (z - a z)` using `h'`. Rewrite `h''`, the goal using `[← sub_eq_zero]`.

Rewrite using `[← h'']`. Normalize the expressions using the abelian group laws. Simplify `congrArg B this` using `only [hB2]`. Use `GlobalTheory.Phase.GaussSum.ph_sum _ (fun m : Λ ⧸ φ.range => ph ((Quotient.out m : Λ) : V)) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m _ beta_reduce`.

Generalize the expression as in `Quotient.out m = x`. Use `set k := Fintype.card (Λ ⧸ φ.range)`. Establish `hk : 0 < k` using `Fintype.card_pos`. Establish `h0 : ((0 : Λ) : Λ ⧸ φ.range) = ((k • x : Λ) : Λ ⧸ φ.range)`. Rewrite using `[QuotientAddGroup.mk_nsmul, card_nsmul_eq_zero]`.

Both sides reduce to the same expression. Take `⟨y, hy, h⟩` from `(hrel _ _).1 h0`. Take `⟨n, hn⟩` from `hint y (hle hy) x x.2`. Establish `hy' : k • B (x : V) = y`. Rewrite using `[← map_nsmul, ← hB2 y]`.

Use `congr 1`. Simplify using `using h`. Establish `e : ((2 * k : ℕ) : ℝ) * (H (B x) x).im = 2 * n`. Rewrite using `[← hn, ← hy', map_nsmul]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Use `⟨2 * k, by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [ph]`. Rewrite using `[mul_pow, ex_pow, e, ex_two, pow_mul, hsq _ x.2]`. Simplify using the standard rewrite rules.

Introduce `x _ y _ z _`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective z`. Simplify using `only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zero, hf, AddSubgroup.coe_add, AddSubgroup.coe_zero]`.

Rewrite using `[hph _ (Λ.add_mem x.2 y.2) _ z.2, hph _ y.2 _ z.2, hph _ x.2 _ z.2, hph0]`. Simplify using `only [map_add, LinearMap.add_apply, Complex.add_im, mul_add, ex_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_phase : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → (∀ x, B (x - a x) = x) → ∀ (Λ Λ' : AddSubgroup V), Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∃ (M : Type) (_ : Fintype M) (s : M → V), (∀ m, s m ∈ Λ) ∧ (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) ∧ GlobalTheory.Phase.Ph (∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ))) := by
  intro V _ _ H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa
  obtain ⟨hα1, hint, hadd⟩ := hα
  have hanti : ∀ x y, (H x y).im = -(H y x).im := fun x y => by rw [hH.1 x y]; simp
  have hself : ∀ x, (H x x).im = 0 := fun x => by have := hanti x x; linarith
  have hadj : ∀ x y, (H (B x) y).im - (H (B y) x).im = (H x y).im := by
    intro x y
    have h1 : H (B x) y + H x (B y) = H x y := by
      have hx := hB1 x
      have hy := hB1 y
      generalize B x = u at hx ⊢
      generalize B y = v at hy ⊢
      subst hx hy
      simp only [map_sub, LinearMap.sub_apply, ha]
      ring
    have h2 := congrArg Complex.im h1
    rw [Complex.add_im, hanti x (B y)] at h2
    linarith
  let ph : V → ℂ := fun x => α x * ex (H (B x) x).im
  have hadd' : ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * ex (H x y).im := hadd
  have hsq : ∀ x ∈ Λ, α x ^ 2 = 1 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hne : ∀ x ∈ Λ, α x ≠ 0 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hα0 : α 0 = 1 := by
    have := hadd' 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hself, ex_zero, mul_one] at this
    exact (mul_eq_left₀ (hne 0 Λ.zero_mem)).1 this.symm
  have hph0 : ph 0 = 1 := by simp [ph, hα0, ex_zero]
  have hph : ∀ x ∈ Λ, ∀ y ∈ Λ, ph (x + y) = ph x * ph y * ex (2 * (H (B x) y).im) := by
    intro x hx y hy
    have e : (H (B (x + y)) (x + y)).im + (H x y).im =
        (H (B x) x).im + (H (B y) y).im + 2 * (H (B x) y).im := by
      simp only [map_add, LinearMap.add_apply, Complex.add_im, ← hadj x y]; ring
    have e' := congrArg ex e
    rw [ex_add, ex_add, ex_add] at e'
    simp only [ph, hadd' x hx y hy]
    linear_combination α x * α y * e'
  have hmem : ∀ y ∈ Λ', y - a y ∈ Λ := fun y hy => Λ.sub_mem (hle hy) (haΛ y hy)
  have hphA : ∀ y ∈ Λ', ph (y - a y) = 1 := by
    intro y hy
    have h := hadd' _ (hmem y hy) _ (haΛ y hy)
    rw [sub_add_cancel, hαa y hy] at h
    have h' : α (y - a y) * ex (H (y - a y) (a y)).im = 1 :=
      (mul_eq_left₀ (hne y (hle hy))).1 (by linear_combination -h)
    obtain ⟨m, hm⟩ := hint y (hle hy) (a y) (haΛ y hy)
    have e1 : (H (y - a y) (a y)).im = m := by
      simp only [map_sub, LinearMap.sub_apply, Complex.sub_im, hself, hm, sub_zero]
    have e2 : (H (B (y - a y)) (y - a y)).im = m + 2 * ((-m : ℤ) : ℝ) := by
      rw [hB2]
      simp only [map_sub, Complex.sub_im, hself, hm]; push_cast; ring
    simp only [ph]
    rw [e2, ex_add, ex_two, mul_one, ← e1, h']
  have hper : ∀ x ∈ Λ, ∀ y ∈ Λ', ph (y - a y + x) = ph x := by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hint y (hle hy) x hx
    rw [hph _ (hmem y hy) x hx, hphA y hy, hB2, hm, ex_two, one_mul, mul_one]
  let φ : Λ'.addSubgroupOf Λ →+ Λ := AddMonoidHom.mk'
    (fun y => ⟨((y : Λ) : V) - a ((y : Λ) : V), hmem _ y.2⟩)
    (fun y z => Subtype.ext (by simp only [AddSubgroup.coe_add, map_add]; abel))
  have hφ : ∀ y, ((φ y : Λ) : V) = ((y : Λ) : V) - a ((y : Λ) : V) := fun _ => rfl
  have hinj : Function.Injective φ := by
    intro y z h
    have := congrArg (fun t : Λ => B (t : V)) h
    simp only [hφ, hB2] at this
    exact Subtype.ext (Subtype.ext this)
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
  have : IsAddTorsionFree V := .of_isTorsionFree ℂ V
  have : Module.Free ℤ Λ := inferInstance
  have := finite_quot _ φ hinj
  let _ : Fintype (Λ ⧸ φ.range) := Fintype.ofFinite _
  have hrel : ∀ x x' : Λ, (x : Λ ⧸ φ.range) = x' ↔ ∃ y ∈ Λ', (x' : V) = y - a y + x := by
    intro x x'
    rw [QuotientAddGroup.eq]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨_, y.2, ?_⟩
      have := congrArg Subtype.val hy
      rw [hφ] at this
      erw [this]; simp
    · rintro ⟨y, hy, h⟩
      refine ⟨⟨⟨y, hle hy⟩, hy⟩, Subtype.ext ?_⟩
      rw [hφ]; simp [h]
  have hf : ∀ x : Λ, ph ((Quotient.out (x : Λ ⧸ φ.range) : Λ) : V) = ph x := by
    intro x
    obtain ⟨y, hy, h⟩ := (hrel x _).1 (QuotientAddGroup.out_eq' _).symm
    rw [h, hper _ x.2 y hy]
  refine ⟨Λ ⧸ φ.range, inferInstance, fun m => ((Quotient.out m : Λ) : V), fun m => (Quotient.out m).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, h⟩ := (hrel ⟨x, hx⟩ _).1 (QuotientAddGroup.out_eq' _).symm
    refine ⟨(((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range), ⟨y, hy⟩), by simp only [h]; abel, ?_⟩
    rintro ⟨m, z, hz⟩ h'
    simp only at h'
    have hm : ((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range) = m := by
      rw [← QuotientAddGroup.out_eq' m, hrel]
      exact ⟨z, hz, by simp only [h']; abel⟩
    subst hm
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [h] at h'
    have : z - a z = y - a y := by
      have h'' : x = y - a y + x - (z - a z) := h'
      rw [← sub_eq_zero] at h'' ⊢
      rw [← h'']; abel
    simpa only [hB2] using congrArg B this
  · refine GlobalTheory.Phase.GaussSum.ph_sum _ (fun m : Λ ⧸ φ.range => ph ((Quotient.out m : Λ) : V)) ⟨?_, ?_⟩
    · intro m _
      beta_reduce
      generalize Quotient.out m = x
      set k := Fintype.card (Λ ⧸ φ.range)
      have hk : 0 < k := Fintype.card_pos
      have h0 : ((0 : Λ) : Λ ⧸ φ.range) = ((k • x : Λ) : Λ ⧸ φ.range) := by
        rw [QuotientAddGroup.mk_nsmul, card_nsmul_eq_zero]; rfl
      obtain ⟨y, hy, h⟩ := (hrel _ _).1 h0
      obtain ⟨n, hn⟩ := hint y (hle hy) x x.2
      have hy' : k • B (x : V) = y := by
        rw [← map_nsmul, ← hB2 y]; congr 1; simpa using h
      have e : ((2 * k : ℕ) : ℝ) * (H (B x) x).im = 2 * n := by
        rw [← hn, ← hy', map_nsmul]; simp; ring
      refine ⟨2 * k, by omega, ?_⟩
      simp only [ph]
      rw [mul_pow, ex_pow, e, ex_two, pow_mul, hsq _ x.2]; simp
    · intro x _ y _ z _
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective z
      simp only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zero, hf, AddSubgroup.coe_add,
        AddSubgroup.coe_zero]
      rw [hph _ (Λ.add_mem x.2 y.2) _ z.2, hph _ y.2 _ z.2, hph _ x.2 _ z.2, hph0]
      simp only [map_add, LinearMap.add_apply, Complex.add_im, mul_add, ex_add]
      ring

end GlobalTheory.UnitaryTheta.GaussPhase
