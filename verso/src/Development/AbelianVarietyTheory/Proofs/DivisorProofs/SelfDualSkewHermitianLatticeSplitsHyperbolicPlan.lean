import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewSplit

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])`.
-/
theorem sig_sig [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

/- English proof (translation)
Simplify using `[form, add_dotProduct]`.
-/
theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J (a • x) y = a * form σ J x y := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Simplify using `only [form, Pi.add_apply, map_add]`. Rewrite using `[show (fun i => σ (y i) + σ (y' i)) = (fun i => σ (y i)) + (fun i => σ (y' i)) from rfl, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    form σ J x (y + y') = form σ J x y + form σ J x y' := by
  simp only [form, Pi.add_apply, map_add]
  rw [show (fun i => σ (y i) + σ (y' i)) = (fun i => σ (y i)) + (fun i => σ (y' i)) from rfl,
    Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [form, Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[show (fun i => σ a * σ (y i)) = σ a • (fun i => σ (y i)) from rfl, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J x (a • y) = σ a * form σ J x y := by
  simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ a * σ (y i)) = σ a • (fun i => σ (y i)) from rfl,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sig_sig h, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[show σ (J j i) = -J i j from hJ i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_skew [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : σ (form σ J x y) = -form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sig_sig h, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show σ (J j i) = -J i j from hJ i j]
  ring

/- English proof (translation)
Introduce `E _ _ n L hL x hx`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h'`.

Use `push_neg at h'`. Conclude with `hx (funext h')`. Establish `hP : L.map (LinearMap.proj (R` using `𝓞 E) (φ := fun _ : Fin n => E) i) = ⊤ := by`. Rewrite using `[eq_top_iff]`. Introduce and unpack `e -`.

Use `⟨(e / x i) • x, h _, ?_⟩` and prove the remaining obligations. Simplify using `[div_mul_cancel₀ _ hi]`. Establish `hfin : Module.Finite (𝓞 E) E` using `⟨by rw [← hP]; exact hL.map _⟩`. Use `haveI : Algebra.IsIntegral (𝓞 E) E := Algebra.IsIntegral.of_finite _ _`. Conclude with `NumberField.RingOfIntegers.not_isField E (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))`.
-/
theorem fg_no_line : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, x ≠ 0 → ∃ s : E, s • x ∉ L := by
  intro E _ _ n L hL x hx
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hx (funext h')
  have hP : L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i) = ⊤ := by
    rw [eq_top_iff]
    rintro e -
    refine ⟨(e / x i) • x, h _, ?_⟩
    simp [div_mul_cancel₀ _ hi]
  have hfin : Module.Finite (𝓞 E) E := ⟨by rw [← hP]; exact hL.map _⟩
  haveI : Algebra.IsIntegral (𝓞 E) E := Algebra.IsIntegral.of_finite _ _
  exact NumberField.RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

/- English proof (translation)
Introduce `E _ _ n φ L hL hne`. Set `φO : (Fin n → E) →ₗ[𝓞 E] E` to `φ.restrictScalars (𝓞 E)`. Set `I : Submodule (𝓞 E) E` to `L.map φO`. Set `If : FractionalIdeal (𝓞 E)⁰ E` to `⟨I, FractionalIdeal.isFractional_of_fg (hL.map φO)⟩`. Establish `hIf : ∀ e, e ∈ If ↔ e ∈ I` using `fun e => Iff.rfl`.

Establish `hI0 : If ≠ 0`. Introduce `h`. Take `⟨z, hz, hφz⟩` from `hne`. Establish `hm : φ z ∈ If` using `(hIf _).2 ⟨z, hz, rfl⟩`. Rewrite `hm` using `[h, FractionalIdeal.mem_zero_iff]`.

Conclude with `hφz hm`. Set `T : Submodule (𝓞 E) (Fin n → E)` to `{ carrier := {w | ∀ z ∈ L, φ z • w ∈ L} add_mem' := fun {a b} ha hb z hz => by rw [smul_add]; exact L.add_mem (ha z hz) (hb z hz) zero_mem' := fun z _ => by rw [smul_zero]; exact L.zero_mem smul_mem' := fun c w hw z hz => by rw [smul_comm]; exact L.smul_mem c (hw z hz) }`. Establish `hle : ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I ≤ T.map φO`. Rewrite using `[Submodule.mul_le]`. Introduce `m hm e he`.

Take `⟨z', hz', rfl⟩` from `he`. Use `⟨m • z', ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `h1` using `(FractionalIdeal.mem_inv_iff hI0).1 hm (φ z) ((hIf _).2 ⟨z, hz, rfl⟩)`. Take `⟨a, ha⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`.

Establish `: φ z • m • z' = a • z'`. Rewrite using `[smul_smul, mul_comm, ← ha, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `L.smul_mem a hz'`. Use `show φ (m • z') = m * φ z'`.

Rewrite using `[map_smul, smul_eq_mul]`. Establish `h1 : (1 : E) ∈ ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I`. Establish `: ((If⁻¹ * If : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I` using `FractionalIdeal.coe_mul _ _`. Rewrite using `[← this, inv_mul_cancel₀ hI0]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`.

Take `⟨y₀, hy₀T, hy₀⟩` from `hle h1`. Conclude with `⟨y₀, hy₀, hy₀T⟩`.
-/
theorem exists_partner : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : (Fin n → E) →ₗ[E] E)
    (L : Submodule (𝓞 E) (Fin n → E)), L.FG → (∃ z ∈ L, φ z ≠ 0) →
    ∃ y₀ : Fin n → E, φ y₀ = 1 ∧ ∀ z ∈ L, φ z • y₀ ∈ L := by
  intro E _ _ n φ L hL hne
  let φO : (Fin n → E) →ₗ[𝓞 E] E := φ.restrictScalars (𝓞 E)
  let I : Submodule (𝓞 E) E := L.map φO
  let If : FractionalIdeal (𝓞 E)⁰ E := ⟨I, FractionalIdeal.isFractional_of_fg (hL.map φO)⟩
  have hIf : ∀ e, e ∈ If ↔ e ∈ I := fun e => Iff.rfl
  have hI0 : If ≠ 0 := by
    intro h
    obtain ⟨z, hz, hφz⟩ := hne
    have hm : φ z ∈ If := (hIf _).2 ⟨z, hz, rfl⟩
    rw [h, FractionalIdeal.mem_zero_iff] at hm
    exact hφz hm
  let T : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {w | ∀ z ∈ L, φ z • w ∈ L}
      add_mem' := fun {a b} ha hb z hz => by rw [smul_add]; exact L.add_mem (ha z hz) (hb z hz)
      zero_mem' := fun z _ => by rw [smul_zero]; exact L.zero_mem
      smul_mem' := fun c w hw z hz => by rw [smul_comm]; exact L.smul_mem c (hw z hz) }
  have hle : ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I ≤ T.map φO := by
    rw [Submodule.mul_le]
    intro m hm e he
    obtain ⟨z', hz', rfl⟩ := he
    refine ⟨m • z', ?_, ?_⟩
    · intro z hz
      have h1 := (FractionalIdeal.mem_inv_iff hI0).1 hm (φ z) ((hIf _).2 ⟨z, hz, rfl⟩)
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 h1
      have : φ z • m • z' = a • z' := by
        rw [smul_smul, mul_comm, ← ha, algebraMap_smul]
      rw [this]
      exact L.smul_mem a hz'
    · show φ (m • z') = m * φ z'
      rw [map_smul, smul_eq_mul]
  have h1 : (1 : E) ∈ ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I := by
    have : ((If⁻¹ * If : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((If⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) * I :=
      FractionalIdeal.coe_mul _ _
    rw [← this, inv_mul_cancel₀ hI0]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨y₀, hy₀T, hy₀⟩ := hle h1
  exact ⟨y₀, hy₀, hy₀T⟩

/- English proof (translation)
Introduce `F E _ _ _ σ n₁ J x y hxx hyy hxy hyx`. Set `fl : (Fin (n₁ + 2) → E) → (Fin (n₁ + 2) → E) →ₗ[E] E` to `fun w => { toFun := fun z => form σ J z w map_add' := fun a b => form_add_left σ J a b w map_smul' := fun a b => form_smul_left σ J a b w }`. Set `Φ : (Fin (n₁ + 2) → E) →ₗ[E] (Fin 2 → E)` to `LinearMap.pi ![fl x, fl y]`. Establish `hΦ : ∀ z, Φ z = ![form σ J z x, form σ J z y]`. Apply the tactic sequence `intro z; ext k; fin_cases k <;> rfl`.

Establish `hsurj : LinearMap.range Φ = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`. Use `⟨v 1 • x + (-v 0) • y, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`.

Use extensionality with `k`. Use `fin_cases k`. Simplify using `only [form_add_left, form_smul_left, hxx, hyx]`. Simplify using the standard rewrite rules. Simplify using `only [form_add_left, form_smul_left, hxy, hyy]`.

Simplify using the standard rewrite rules. Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker Φ`. Rewrite `hrk` using `[hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Establish `hK : Module.finrank E (LinearMap.ker Φ) = n₁` using `by omega`. Set `b` to `Module.finBasisOfFinrankEq E (LinearMap.ker Φ) hK`.

Set `ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E` to `Matrix.of fun i j => (b j : Fin (n₁ + 2) → E) i`. Establish `hι : ∀ u, ι *ᵥ u = ((b.equivFun.symm u : LinearMap.ker Φ) : Fin (n₁ + 2) → E)`. Introduce `u`. Use extensionality with `i`. Simplify using `[ι, Module.Basis.equivFun_symm_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Establish `hker : ∀ k : LinearMap.ker Φ, form σ J (k : Fin (n₁ + 2) → E) x = 0 ∧ form σ J (k : Fin (n₁ + 2) → E) y = 0`. Introduce `k`. Establish `h0` using `LinearMap.mem_ker.mp k.2`. Rewrite `h0` using `[hΦ]`. Conclude with `⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩`.

Use `⟨ι, fun u => by rw [hι]; exact hker _, ?_, ?_⟩` and prove the remaining obligations. Introduce `u u' h`. Rewrite `h` using `[hι, hι]`. Conclude with `b.equivFun.symm.injective (Subtype.ext h)`. Introduce `z set w := z + (-form σ J z y) • x + form σ J z x • y with hw`.

Establish `hwK : w ∈ LinearMap.ker Φ`. Rewrite using `[LinearMap.mem_ker, hΦ]`. Use extensionality with `k`. Use `fin_cases k`. Simplify using `only [hw, form_add_left, form_smul_left, hxx, hyx]`.

Simplify using the standard rewrite rules. Simplify using `only [hw, form_add_left, form_smul_left, hxy, hyy]`. Simplify using the standard rewrite rules. Use `⟨b.equivFun ⟨w, hwK⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hι, LinearEquiv.symm_apply_apply]`.

Use extensionality with `i`. Simplify using `only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_complement : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n₁ : ℕ)
    (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (x y : Fin (n₁ + 2) → E),
    form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 → form σ J y x = -1 →
    ∃ ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E, (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      Function.Injective ι.mulVec ∧ ∀ z, ∃ u, z = form σ J z y • x + ι *ᵥ u + (-form σ J z x) • y := by
  intro F E _ _ _ σ n₁ J x y hxx hyy hxy hyx
  let fl : (Fin (n₁ + 2) → E) → (Fin (n₁ + 2) → E) →ₗ[E] E := fun w =>
    { toFun := fun z => form σ J z w
      map_add' := fun a b => form_add_left σ J a b w
      map_smul' := fun a b => form_smul_left σ J a b w }
  let Φ : (Fin (n₁ + 2) → E) →ₗ[E] (Fin 2 → E) := LinearMap.pi ![fl x, fl y]
  have hΦ : ∀ z, Φ z = ![form σ J z x, form σ J z y] := by
    intro z; ext k; fin_cases k <;> rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    refine ⟨v 1 • x + (-v 0) • y, ?_⟩
    rw [hΦ]
    ext k; fin_cases k
    · simp only [form_add_left, form_smul_left, hxx, hyx]; simp
    · simp only [form_add_left, form_smul_left, hxy, hyy]; simp
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
  have hK : Module.finrank E (LinearMap.ker Φ) = n₁ := by omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker Φ) hK
  let ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E := Matrix.of fun i j => (b j : Fin (n₁ + 2) → E) i
  have hι : ∀ u, ι *ᵥ u = ((b.equivFun.symm u : LinearMap.ker Φ) : Fin (n₁ + 2) → E) := by
    intro u
    ext i
    simp [ι, Module.Basis.equivFun_symm_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hker : ∀ k : LinearMap.ker Φ, form σ J (k : Fin (n₁ + 2) → E) x = 0 ∧ form σ J (k : Fin (n₁ + 2) → E) y = 0 := by
    intro k
    have h0 := LinearMap.mem_ker.mp k.2
    rw [hΦ] at h0
    exact ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
  refine ⟨ι, fun u => by rw [hι]; exact hker _, ?_, ?_⟩
  · intro u u' h
    rw [hι, hι] at h
    exact b.equivFun.symm.injective (Subtype.ext h)
  · intro z
    set w := z + (-form σ J z y) • x + form σ J z x • y with hw
    have hwK : w ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker, hΦ]
      ext k; fin_cases k
      · simp only [hw, form_add_left, form_smul_left, hxx, hyx]; simp
      · simp only [hw, form_add_left, form_smul_left, hxy, hyy]; simp
    refine ⟨b.equivFun ⟨w, hwK⟩, ?_⟩
    rw [hι, LinearEquiv.symm_apply_apply]
    ext i
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ θ hθ n₁ J L hJ hL hSD x hx hxx`. Establish `hsk` using `form_skew hσ hJ`. Establish `hOs : ∀ (a : 𝓞 E) (c : E), c • x ∈ L → ((a : E) * c) • x ∈ L`. Introduce `a c h`. Use `L.smul_mem a h` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[Algebra.smul_def, mul_assoc]`. Set `φ : (Fin (n₁ + 2) → E) →ₗ[E] E` to `{ toFun := fun z => form σ J z x map_add' := fun a b => form_add_left σ J a b x map_smul' := fun a b => form_smul_left σ J a b x }`. Establish `hφ : ∀ z, φ z = form σ J z x` using `fun _ => rfl`.

Establish `hnd : ∃ z ∈ L, φ z ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ z, form σ J z x = 0`. Introduce `z`.

Establish `hz : z ∈ Submodule.span E (L : Set (Fin (n₁ + 2) → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw => exact hcon w hw`.

Consider the case `zero => simp [form]`. Consider the case `add a b _ _ ha hb => rw [form_add_left, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [form_smul_left, ha, mul_zero]`. Take `⟨s, hs⟩` from `fg_no_line E _ L hL.fg x hx`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[hSD]`. Introduce `w _ o`. Establish `h0 : form σ J (s • x) w = 0`. Rewrite using `[form_smul_left]`. Establish `h1` using `hsk w x`.

Rewrite `h1` using `[hall w, map_zero]`. Rewrite using `[neg_eq_zero.mp h1.symm, mul_zero]`. Rewrite using `[h0, mul_zero, map_zero]`. Conclude with `isIntegral_zero`. Take `⟨y₀, hy₀1, hy₀L⟩` from `exists_partner E _ φ L hL.fg hnd`.

Simplify using `only [hφ] at hy₀1 hy₀L`. Establish `hxy₀ : form σ J x y₀ = -1`. Use `hsk y₀ x` as an intermediate fact. Rewrite `this` using `[hy₀1, map_one]`. Take the linear combination `this`.

Establish `hb : ∀ z ∈ L, form σ J z y₀ • x ∈ L`. Introduce `z hz`. Rewrite using `[hSD]`. Introduce `w hw o`. Establish `key` using `(hSD z).1 hz _ (hy₀L w hw) (-o)`.

Rewrite `key` using `[form_smul_right]`. Establish `h1` using `hsk w x`. Rewrite using `[form_smul_left, show form σ J x w = -σ (form σ J w x) by rw [h1, neg_neg]]`. Establish `e : (o : E) * (form σ J z y₀ * -σ (form σ J w x)) = ((-o : 𝓞 E) : E) * (σ (form σ J w x) * form σ J z y₀)` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `key`. Use `set q := form σ J y₀ y₀ with hq`. Establish `hσq : σ q = -q` using `hsk y₀ y₀`. Establish `hσθ : σ (θ : E) = 1 - θ` using `by linear_combination hθ`. Use `set y : Fin (n₁ + 2) → E := (-1 : E) • y₀ + (-((θ : E) * q)) • x with hy`.

Establish `hxy : form σ J x y = 1`. Rewrite using `[hy, form_add_right, form_smul_right, form_smul_right, hxy₀, hxx]`. Simplify using the standard rewrite rules. Establish `hyx : form σ J y x = -1`. Rewrite using `[hy, form_add_left, form_smul_left, form_smul_left, hy₀1, hxx]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hyy : form σ J y y = 0`. Rewrite using `[hy]`. Simplify using `only [form_add_left, form_add_right, form_smul_left, form_smul_right]`. Rewrite using `[← hq, hy₀1, hxy₀, hxx]`.

Simplify using `only [map_neg, map_one, map_mul, hσq, hσθ]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ι, hι1, hιinj, hιdec⟩` from `exists_complement F E σ n₁ J x y hxx hyy hxy hyx`. Use `⟨y, ι, hxy, hyy, hι1, ?_, ?_⟩` and prove the remaining obligations. Introduce `s t u h`.

Establish `e1 : form σ J (s • x + ι *ᵥ u + t • y) x = 0` using `by rw [h]; simp [form]`. Establish `e2 : form σ J (s • x + ι *ᵥ u + t • y) y = 0` using `by rw [h]; simp [form]`. Rewrite `e1` using `[form_add_left, form_add_left, form_smul_left, form_smul_left, hxx, (hι1 u).1, hyx]`. Rewrite `e2` using `[form_add_left, form_add_left, form_smul_left, form_smul_left, hxy, (hι1 u).2, hyy]`. Establish `ht : t = 0` using `by linear_combination -e1`.

Establish `hs : s = 0` using `by linear_combination e2`. Substitute `ht hs` using the available equality. Use `⟨rfl, rfl, hιinj ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_zero]`. Simplify using `using h`.

Introduce `z hz`. Take `⟨u, hu⟩` from `hιdec z`. Establish `hzq : (form σ J z x * q) • x ∈ L`. Use `hb _ (hy₀L z hz)` as an intermediate fact. Rewrite `this` using `[form_smul_left]`. Then use the resulting hypothesis.

Establish `hsx : form σ J z y • x ∈ L`. Establish `hsv : form σ J z y = (-1) * form σ J z y₀ + ((1 - θ : 𝓞 E) : E) * (form σ J z x * q)`. Rewrite using `[hy, form_add_right, form_smul_right, form_smul_right]`. Simplify using `only [map_neg, map_one, map_mul, hσq, hσθ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsv, add_smul]`. Use `L.add_mem ?_ (hOs _ _ hzq)` and prove the remaining obligations. Use `hOs (-1) _ (hb z hz)` as an intermediate fact. Simplify using `using this`.

Establish `hty : (-form σ J z x) • y ∈ L`. Establish `: (-form σ J z x) • y = form σ J z x • y₀ + ((θ : E) * (form σ J z x * q)) • x`. Rewrite using `[hy, smul_add, smul_smul, smul_smul]`. Use `congr 1`. Simplify using the standard rewrite rules.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.add_mem (hy₀L z hz) (hOs _ _ hzq)`. Use `⟨form σ J z y, -form σ J z x, u, hsx, hty, ?_, hu⟩` and prove the remaining obligations.

Establish `: ι *ᵥ u = z - form σ J z y • x - (-form σ J z x) • y`. Generalize the expression as in `form σ J z y = s at hu ⊢`. Generalize the expression as in `-form σ J z x = t at hu ⊢`. Rewrite using `[hu]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `L.sub_mem (L.sub_mem hz hsx) hty`.
-/
theorem split_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E)), (∀ i j, σ (J j i) = -J i j) → L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    ∀ x : Fin (n₁ + 2) → E, x ≠ 0 → form σ J x x = 0 →
    ∃ (y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E), form σ J x y = 1 ∧ form σ J y y = 0 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) ∧
      ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y := by
  intro F E _ _ _ _ _ σ hσ θ hθ n₁ J L hJ hL hSD x hx hxx
  have hsk := form_skew hσ hJ

  have hOs : ∀ (a : 𝓞 E) (c : E), c • x ∈ L → ((a : E) * c) • x ∈ L := by
    intro a c h
    have := L.smul_mem a h
    convert this using 1
    ext i; simp [Algebra.smul_def, mul_assoc]

  let φ : (Fin (n₁ + 2) → E) →ₗ[E] E :=
    { toFun := fun z => form σ J z x
      map_add' := fun a b => form_add_left σ J a b x
      map_smul' := fun a b => form_smul_left σ J a b x }
  have hφ : ∀ z, φ z = form σ J z x := fun _ => rfl

  have hnd : ∃ z ∈ L, φ z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ z, form σ J z x = 0 := by
      intro z
      have hz : z ∈ Submodule.span E (L : Set (Fin (n₁ + 2) → E)) := by
        rw [hL.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem w hw => exact hcon w hw
      | zero => simp [form]
      | add a b _ _ ha hb => rw [form_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [form_smul_left, ha, mul_zero]
    obtain ⟨s, hs⟩ := fg_no_line E _ L hL.fg x hx
    apply hs
    rw [hSD]
    intro w _ o
    have h0 : form σ J (s • x) w = 0 := by
      rw [form_smul_left]
      have h1 := hsk w x
      rw [hall w, map_zero] at h1
      rw [neg_eq_zero.mp h1.symm, mul_zero]
    rw [h0, mul_zero, map_zero]
    exact isIntegral_zero
  obtain ⟨y₀, hy₀1, hy₀L⟩ := exists_partner E _ φ L hL.fg hnd
  simp only [hφ] at hy₀1 hy₀L
  have hxy₀ : form σ J x y₀ = -1 := by
    have := hsk y₀ x
    rw [hy₀1, map_one] at this
    linear_combination this

  have hb : ∀ z ∈ L, form σ J z y₀ • x ∈ L := by
    intro z hz
    rw [hSD]
    intro w hw o
    have key := (hSD z).1 hz _ (hy₀L w hw) (-o)
    rw [form_smul_right] at key
    have h1 := hsk w x
    rw [form_smul_left, show form σ J x w = -σ (form σ J w x) by rw [h1, neg_neg]]
    have e : (o : E) * (form σ J z y₀ * -σ (form σ J w x)) = ((-o : 𝓞 E) : E) * (σ (form σ J w x) * form σ J z y₀) := by
      push_cast; ring
    rw [e]; exact key
  set q := form σ J y₀ y₀ with hq
  have hσq : σ q = -q := hsk y₀ y₀
  have hσθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  set y : Fin (n₁ + 2) → E := (-1 : E) • y₀ + (-((θ : E) * q)) • x with hy
  have hxy : form σ J x y = 1 := by
    rw [hy, form_add_right, form_smul_right, form_smul_right, hxy₀, hxx]; simp
  have hyx : form σ J y x = -1 := by
    rw [hy, form_add_left, form_smul_left, form_smul_left, hy₀1, hxx]; ring
  have hyy : form σ J y y = 0 := by
    rw [hy]
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right]
    rw [← hq, hy₀1, hxy₀, hxx]
    simp only [map_neg, map_one, map_mul, hσq, hσθ]
    ring
  obtain ⟨ι, hι1, hιinj, hιdec⟩ := exists_complement F E σ n₁ J x y hxx hyy hxy hyx
  refine ⟨y, ι, hxy, hyy, hι1, ?_, ?_⟩
  · intro s t u h
    have e1 : form σ J (s • x + ι *ᵥ u + t • y) x = 0 := by rw [h]; simp [form]
    have e2 : form σ J (s • x + ι *ᵥ u + t • y) y = 0 := by rw [h]; simp [form]
    rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hxx, (hι1 u).1, hyx] at e1
    rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hxy, (hι1 u).2, hyy] at e2
    have ht : t = 0 := by linear_combination -e1
    have hs : s = 0 := by linear_combination e2
    subst ht hs
    refine ⟨rfl, rfl, hιinj ?_⟩
    rw [Matrix.mulVec_zero]
    simpa using h
  · intro z hz
    obtain ⟨u, hu⟩ := hιdec z
    have hzq : (form σ J z x * q) • x ∈ L := by
      have := hb _ (hy₀L z hz)
      rwa [form_smul_left] at this
    have hsx : form σ J z y • x ∈ L := by
      have hsv : form σ J z y = (-1) * form σ J z y₀ + ((1 - θ : 𝓞 E) : E) * (form σ J z x * q) := by
        rw [hy, form_add_right, form_smul_right, form_smul_right]
        simp only [map_neg, map_one, map_mul, hσq, hσθ]
        push_cast; ring
      rw [hsv, add_smul]
      refine L.add_mem ?_ (hOs _ _ hzq)
      have := hOs (-1) _ (hb z hz)
      simpa using this
    have hty : (-form σ J z x) • y ∈ L := by
      have : (-form σ J z x) • y = form σ J z x • y₀ + ((θ : E) * (form σ J z x * q)) • x := by
        rw [hy, smul_add, smul_smul, smul_smul]
        congr 1
        · simp
        · congr 1; ring
      rw [this]
      exact L.add_mem (hy₀L z hz) (hOs _ _ hzq)
    refine ⟨form σ J z y, -form σ J z x, u, hsx, hty, ?_, hu⟩
    have : ι *ᵥ u = z - form σ J z y • x - (-form σ J z x) • y := by
      generalize form σ J z y = s at hu ⊢
      generalize -form σ J z x = t at hu ⊢
      rw [hu]; abel
    rw [this]
    exact L.sub_mem (L.sub_mem hz hsx) hty

end GlobalTheory.PlaneSkewSplit
