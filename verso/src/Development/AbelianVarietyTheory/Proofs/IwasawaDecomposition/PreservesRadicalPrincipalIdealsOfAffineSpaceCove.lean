import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

/- English proof (translation)
Establish `hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a` using `fun a => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Rewrite `h`, the goal using `[MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq]`. Rewrite `h` using `[map_pow]`. Establish `hn` using `(MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩`.

Use extensionality with `i`. Take `⟨k, hk⟩` from `hn i`. Rewrite `hk`, the goal using `[MvPolynomial.coeff_map]`. Rewrite `hk` using `[← map_pow, hq]`. Rewrite using `[MvPolynomial.coeff_zero, hq]`.

Conclude with `hg _ _ hk`.
-/
theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  ext i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  rw [MvPolynomial.coeff_zero, hq]
  exact hg _ _ hk

/- English proof (translation)
Take `⟨U, f, hU, rfl⟩` from `hx`. Establish `hne : (V : Set M.Z).Nonempty` using `⟨z, hz⟩`. Take `⟨g, hgU, hwg⟩` from `hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz`. Establish `hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty` using `⟨z, hwg⟩`. Use `hV.isLocalization_basicOpen g` as an intermediate fact.

Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g (resG M.Z hgU f)`. Establish `h1` using `congrArg (M.res _ hg) ha`. Establish `h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t` using `fun t => M.res_resG (M.Z.basicOpen_le g) hg t`. Rewrite `h1` using `[map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply, RatModel.res_apply]`. Establish `hu` using `(RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)`.

Use `⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩` and prove the remaining obligations. Rewrite using `[← inv_pow]`. Conclude with `pow_mem hu.2 n`.
-/
theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

/- English proof (translation)
Introduce and unpack `z' g ⟨hg0, hgO, hg⟩`. Take `⟨hf, hc⟩` from `h`. Take `⟨U, W, t, hU, -, hz, hW, hinj, hR⟩` from `hc z'`. Establish `hφ0 : φ g ≠ 0` using `(map_ne_zero φ).2 hg0`. Use `⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩` and prove the remaining obligations.

Set `A` to `(M.O (f z')).toSubring`. Set `ψ : MvPolynomial (Fin r) A →+* Ω'` to `MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t`. Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `P hP`.

Use `hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)` as an intermediate fact. Conclude with `(map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this`. Establish `hO : ∀ P, ψ P ∈ M'.O z'` using `fun P => by`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => rw [MvPolynomial.eval₂Hom_C]`.

Conclude with `hf.map_mem_O a.2`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, MvPolynomial.eval₂Hom_X']`.

Conclude with `mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))`. Establish `hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y`. Introduce `y hy`. Rewrite `hy` using `[hR]`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Break down `hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Conclude with `⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩`. Conclude with `⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩`. Consider the case `algebraMap c`.

Conclude with `⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩, (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩`. Consider the case `add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha`. Take `⟨Q, rfl⟩` from `hb`. Conclude with `⟨P + Q, map_add _ _ _⟩`. Consider the case `mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha`.

Take `⟨Q, rfl⟩` from `hb`. Conclude with `⟨P * Q, map_mul _ _ _⟩`. Establish `hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y`. Introduce and unpack `y k ⟨c, hc⟩`. Establish `e : (y : Ω) ^ k = g * c` using `congrArg Subtype.val hc`.

Use `hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)` as an intermediate fact. Conclude with `⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩`. Establish `hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g` using `MvPolynomial.eval₂Hom_C _ _ _`. Take `⟨a, b, ha, hb, hb0, hbi, e1⟩` from `exists_div_of_mem_O hU hz hx`. Take `⟨c, d, hc, hd, hd0, hdi, e2⟩` from `exists_div_of_mem_O hU hz hxn`.

Take `⟨a, rfl⟩` from `hS a ha`. Take `⟨b, rfl⟩` from `hS b hb`. Take `⟨c, rfl⟩` from `hS c hc`. Take `⟨d, rfl⟩` from `hS d hd`. Establish `hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1)`.

Use `⟨c * b ^ n * a * d ^ n, hψ ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, hC, ← e2]`. Rewrite using `[← e1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨Q, hQ⟩` from `C_dvd_of_C_dvd_pow hrad hdvd`. Establish `e3` using `congrArg ψ hQ`. Rewrite `e3` using `[map_mul, map_mul, hC, ← e1]`. Establish `e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e3`. Rewrite using `[e4]`. Conclude with `mul_mem (mul_mem (hO Q) hbi) hdi`.
-/
theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
