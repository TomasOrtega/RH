import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeGalois

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section SlopeTestRemainingChoices

/- English proof (translation)
Rewrite using `[aeval_def, hom_eval₂, aeval_def, eval₂_map]`. Use `congr 1`. Use extensionality with `a`. Conclude with `h a`.
-/
theorem map_aeval_of_comp {A B K K' : Type*} [CommRing A] [CommRing B] [CommRing K]
    [CommRing K'] [Algebra A K] [Algebra B K'] (f : K →+* K') (τ : A →+* B)
    (h : ∀ a, f (algebraMap A K a) = algebraMap B K' (τ a)) (p : A[X]) (z : K) :
    f (aeval z p) = aeval (f z) (p.map τ) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact h a

/- English proof (translation)
Distinguish the cases in `hbb : b = b'`. Substitute `hbb` using the available equality. Conclude with `⟨add_right_cancel h, rfl⟩`. It suffices to derive a contradiction. Apply `genY_not_mem W` to reduce the goal to its premises.

Establish `hne : b - b' ≠ 0` using `sub_ne_zero.mpr hbb`. Establish `e : genY W = (a' - a) / (b - b')`. Rewrite using `[eq_div_iff hne]`. Take the linear combination `h`. Rewrite using `[e]`.

Conclude with `div_mem (sub_mem ha' ha) (sub_mem hb hb')`.
-/
theorem eq_of_add_mul_genY_eq {K : Type*} [Field K] {W : WeierstrassCurve K}
    {a b a' b' : W.toAffine.FunctionField} (ha : a ∈ K⟮genX W⟯) (hb : b ∈ K⟮genX W⟯)
    (ha' : a' ∈ K⟮genX W⟯) (hb' : b' ∈ K⟮genX W⟯)
    (h : a + b * genY W = a' + b' * genY W) : a = a' ∧ b = b' := by
  by_cases hbb : b = b'
  · subst hbb
    exact ⟨add_right_cancel h, rfl⟩
  · exfalso
    apply genY_not_mem W
    have hne : b - b' ≠ 0 := sub_ne_zero.mpr hbb
    have e : genY W = (a' - a) / (b - b') := by
      rw [eq_div_iff hne]
      linear_combination h
    rw [e]
    exact div_mem (sub_mem ha' ha) (sub_mem hb hb')

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ffCongr_aeval {K : Type u} [Field K] {C D : WeierstrassCurve K} (h : C = D) (p : K[X]) :
    ffCongr h (aeval (genX C) p) = aeval (genX D) p := by
  subst h
  rfl

/- English proof (translation)
Substitute `hC hC'` using the available equality. Both sides reduce to the same expression.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_congr {K : Type u} [Field K]
    {C D C' D' : WeierstrassCurve K} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').congr hC.symm hC'.symm = φ := by
  subst hC hC'
  rfl

end SlopeTestRemainingChoices

section Galois

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (E : WeierstrassCurve F)

/- English proof (translation)
Use `map_aeval_of_comp (galFF E g).toRingHom (g : Ω →+* Ω) (fun c => galFF_algebraMap E g c) p (genX (E.baseChange Ω))` as an intermediate fact. Simplify `this` using `[galFF_genX]`.
-/
theorem galFF_aeval (g : Ω ≃ₐ[F] Ω) (p : Polynomial Ω) :
    galFF E g (aeval (genX (E.baseChange Ω)) p) =
      aeval (genX (E.baseChange Ω)) (p.map (g : Ω →+* Ω)) := by
  have := map_aeval_of_comp (galFF E g).toRingHom (g : Ω →+* Ω)
    (fun c => galFF_algebraMap E g c) p (genX (E.baseChange Ω))
  simpa [galFF_genX] using this

/- English proof (translation)
Use `conv_lhs => rw [← RatFunc.num_div_denom r]`. Rewrite using `[ratEmb_div, ratEmb_div, map_div₀, galFF_aeval, galFF_aeval]`.
-/
theorem galFF_ratEmb (g : Ω ≃ₐ[F] Ω) (r : RatFunc Ω) :
    galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω)
      (algebraMap _ _ (r.num.map (g : Ω →+* Ω)) / algebraMap _ _ (r.denom.map (g : Ω →+* Ω))) := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [ratEmb_div, ratEmb_div, map_div₀, galFF_aeval, galFF_aeval]

/- English proof (translation)
Rewrite `h` using `[galFF_ratEmb]`. Establish `h2` using `ratEmb_injective (E.baseChange Ω) h`. Establish `hcop : IsCoprime (r.num.map (g : Ω →+* Ω)) (r.denom.map (g : Ω →+* Ω))`. Simplify using `using r.isCoprime_num_denom.map (mapRingHom (g : Ω →+* Ω))`. Take `⟨h1, h1'⟩` from `num_denom_div_of_isCoprime (r.monic_denom.map (g : Ω →+* Ω)) hcop`.

Rewrite `h1`, `h1'` using `[h2]`. Conclude with `⟨h1.symm, h1'.symm⟩`.
-/
theorem map_eq_of_galFF_ratEmb (g : Ω ≃ₐ[F] Ω) {r : RatFunc Ω}
    (h : galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    r.num.map (g : Ω →+* Ω) = r.num ∧ r.denom.map (g : Ω →+* Ω) = r.denom := by
  rw [galFF_ratEmb] at h
  have h2 := ratEmb_injective (E.baseChange Ω) h
  have hcop : IsCoprime (r.num.map (g : Ω →+* Ω)) (r.denom.map (g : Ω →+* Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (g : Ω →+* Ω))
  obtain ⟨h1, h1'⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (g : Ω →+* Ω)) hcop
  rw [h2] at h1 h1'
  exact ⟨h1.symm, h1'.symm⟩

/- English proof (translation)
Rewrite `ha`, the goal using `[← fieldRange_ratEmb]`. Take `⟨r, rfl⟩` from `ha`. Conclude with `⟨_, (galFF_ratEmb E g r).symm⟩`.
-/
theorem galFF_mem_adjoin_genX (g : Ω ≃ₐ[F] Ω) {a : (E.baseChange Ω).toAffine.FunctionField}
    (ha : a ∈ Ω⟮genX (E.baseChange Ω)⟯) : galFF E g a ∈ Ω⟮genX (E.baseChange Ω)⟯ := by
  rw [← fieldRange_ratEmb] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  exact ⟨_, (galFF_ratEmb E g r).symm⟩

end Galois

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [IsAlgClosed Ω] in
/- English proof (translation)
The claim follows from `WeierstrassCurve.map_baseChange (R := F) (S := F) W (IsScalarTower.toAlgHom F F₁ Ω)`.
-/
theorem map_toAlgHom_baseChange (F₁ : IntermediateField F Ω) (W : WeierstrassCurve F) :
    (W.baseChange F₁).map (algebraMap F₁ Ω) = W.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) W (IsScalarTower.toAlgHom F F₁ Ω)

/- English proof (translation)
Use `haveI : IsAlgClosed (algebraicClosure F Ω) := IsAlgClosure.isAlgClosed F`. Establish `hc` using `(mem_bot_iff_forall_algEquiv_apply_eq (F := algebraicClosure F Ω)).mpr h`. Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.mp hc`. Conclude with `mem_algebraicClosure_iff.mp a.2`.
-/
theorem isAlgebraic_of_forall_algEquiv {c : Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, g c = c) : IsAlgebraic F c := by
  haveI : IsAlgClosed (algebraicClosure F Ω) := IsAlgClosure.isAlgClosed F
  have hc := (mem_bot_iff_forall_algEquiv_apply_eq (F := algebraicClosure F Ω)).mpr h
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hc
  exact mem_algebraicClosure_iff.mp a.2

/- English proof (translation)
Introduce `c hc`. Apply `isAlgebraic_of_forall_algEquiv` to reduce the goal to its premises. Introduce `g`. Take `⟨h1, h2⟩` from `map_eq_of_galFF_ratEmb E (g.restrictScalars F) (h g)`. Break down `Finset.mem_union.mp hc with hc | hc` into its components or cases.

Take `⟨n, -, rfl⟩` from `Polynomial.mem_coeffs_iff.mp hc`. Use `congrArg (coeff · n) h1` as an intermediate fact. Simplify using `using this`. Take `⟨n, -, rfl⟩` from `Polynomial.mem_coeffs_iff.mp hc`. Use `congrArg (coeff · n) h2` as an intermediate fact.

Simplify using `using this`.
-/
theorem isAlgebraic_coeffs [DecidableEq Ω] {r : RatFunc Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    ∀ c ∈ r.num.coeffs ∪ r.denom.coeffs, IsAlgebraic F c := by
  intro c hc
  apply isAlgebraic_of_forall_algEquiv
  intro g
  obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb E (g.restrictScalars F) (h g)
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (coeff · n) h1
    simpa using this
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (coeff · n) h2
    simpa using this

omit [IsAlgClosed Ω] in
/- English proof (translation)
Rewrite using `[← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : p.coeff n = 0`. Conclude with `⟨0, by rw [hn, map_zero]⟩`. Conclude with `⟨⟨p.coeff n, IntermediateField.subset_adjoin F _ (hp (coeff_mem_coeffs hn))⟩, rfl⟩`.
-/
theorem exists_map_eq_of_coeffs {S : Finset Ω} {p : Polynomial Ω} (hp : p.coeffs ⊆ S) :
    ∃ p₁ : Polynomial (IntermediateField.adjoin F (S : Set Ω)),
      p₁.map (algebraMap (IntermediateField.adjoin F (S : Set Ω)) Ω) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases hn : p.coeff n = 0
  · exact ⟨0, by rw [hn, map_zero]⟩
  · exact ⟨⟨p.coeff n, IntermediateField.subset_adjoin F _ (hp (coeff_mem_coeffs hn))⟩, rfl⟩

/- English proof (translation)
Establish `hfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, ψ.conj (g.restrictScalars F) = ψ` using `fun g => ψ.conj_eq_self _ (fun z hz => g.commutes ⟨z, mem_algebraicClosure_iff.mpr hz⟩)`. Establish `hxfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.x = ψ.x` using `fun g => by rw [← Isogeny.conj_alt_bis, hfix g]`. Establish `hyfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.y = ψ.y` using `fun g => by rw [← Isogeny.conj_y, hfix g]`. Take `⟨r, hr⟩` from `ψ.exists_ratEmb_eq_x`. Take `⟨a, b, ha, hb, hab⟩` from `exists_eq_add_mul_genY (E.baseChange Ω) ψ.y`.

Establish `ha'` using `ha`. Establish `hb'` using `hb`. Rewrite `ha'`, `hb'` using `[← fieldRange_ratEmb]`. Take `⟨r₂, hr₂⟩` from `ha'`. Take `⟨r₃, hr₃⟩` from `hb'`.

Express the relevant statement in the definitionally equal form `ratEmb (E.baseChange Ω) r₂ = a at hr₂`. Express the relevant statement in the definitionally equal form `ratEmb (E.baseChange Ω) r₃ = b at hr₃`. Establish `hab_fix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) a = a ∧ galFF E (g.restrictScalars F) b = b`. Introduce `g`. Establish `e` using `hyfix g`.

Rewrite `e` using `[hab, map_add, map_mul, galFF_genY]`. Conclude with `eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX E _ ha) (galFF_mem_adjoin_genX E _ hb) ha hb e`. Establish `h1` using `isAlgebraic_coeffs (E := E) (r := r) (fun g => by rw [hr]; exact hxfix g)`. Establish `h2` using `isAlgebraic_coeffs (E := E) (r := r₂) (fun g => by rw [hr₂]; exact (hab_fix g).1)`. Establish `h3` using `isAlgebraic_coeffs (E := E) (r := r₃) (fun g => by rw [hr₃]; exact (hab_fix g).2)`.

Use `set S : Finset Ω := (r.num.coeffs ∪ r.denom.coeffs) ∪ (r₂.num.coeffs ∪ r₂.denom.coeffs) ∪ (r₃.num.coeffs ∪ r₃.denom.coeffs) with hS`. Establish `hSalg : ∀ c ∈ (S : Set Ω), _root_.IsIntegral F c`. Introduce `c hc`. Break down `Finset.mem_union.mp hc with hc | hc` into its components or cases. Break down `Finset.mem_union.mp hc with hc | hc` into its components or cases.

Conclude with `(h1 c hc).isIntegral`. Conclude with `(h2 c hc).isIntegral`. Conclude with `(h3 c hc).isIntegral`. Use `set F₁ := IntermediateField.adjoin F (S : Set Ω)`. Use `haveI : FiniteDimensional F F₁ := IntermediateField.finiteDimensional_adjoin hSalg`.

Take `⟨n₁, hn₁⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r.num) (fun c hc => by simp [hS, hc])`. Take `⟨d₁, hd₁⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r.denom) (fun c hc => by simp [hS, hc])`. Take `⟨n₂, hn₂⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.num) (fun c hc => by simp [hS, hc])`. Take `⟨d₂, hd₂⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.denom) (fun c hc => by simp [hS, hc])`. Take `⟨n₃, hn₃⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.num) (fun c hc => by simp [hS, hc])`.

Take `⟨d₃, hd₃⟩` from `exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.denom) (fun c hc => by simp [hS, hc])`. Use `set σ₁ := algebraMap F₁ Ω`. Use `set C₁ := E.baseChange F₁`. Establish `h` using `map_toAlgHom_baseChange F₁ E`. Establish `h'` using `map_toAlgHom_baseChange F₁ E'`.

Use `set ψ₁ := ψ.congr h.symm h'.symm`. Use `set X₁ := genX C₁`. Use `set x₁ : C₁.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁`. Use `set y₁ : C₁.toAffine.FunctionField := aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY C₁`. Establish `hrat : ∀ (s : RatFunc Ω) (p q : Polynomial F₁), p.map σ₁ = s.num → q.map σ₁ = s.denom → ffMap σ₁ C₁ (aeval X₁ p / aeval X₁ q) = ffCongr h.symm (ratEmb (E.baseChange Ω) s)`.

Introduce `s p q hp hq`. Use `conv_rhs => rw [← RatFunc.num_div_denom s]`. Rewrite using `[ratEmb_div, map_div₀, map_div₀, ffCongr_aeval, ffCongr_aeval, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]`. Establish `hx₁ : ffMap σ₁ C₁ x₁ = ψ₁.x`. Rewrite using `[Isogeny.congr_alt, ← hr]`.

Conclude with `hrat r n₁ d₁ hn₁ hd₁`. Establish `hy₁ : ffMap σ₁ C₁ y₁ = ψ₁.y`. Rewrite using `[Isogeny.congr_y, hab, map_add, map_mul, ← hr₂, ← hr₃, map_add, map_mul, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃, ffMap_genY, ffCongr_genY]`. Use `⟨F₁, inferInstance, Isogeny.ofMap σ₁ ψ₁ x₁ y₁ hx₁ hy₁, h, h', ?_⟩` and prove the remaining obligations. Rewrite using `[Isogeny.mapOf, Isogeny.map_ofMap]`.

Conclude with `Isogeny.congr_congr h.symm h'.symm ψ`.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_finiteDimensional_mapOf_eq
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  classical
  have hfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, ψ.conj (g.restrictScalars F) = ψ :=
    fun g => ψ.conj_eq_self _ (fun z hz => g.commutes ⟨z, mem_algebraicClosure_iff.mpr hz⟩)
  have hxfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.x = ψ.x :=
    fun g => by rw [← Isogeny.conj_alt_bis, hfix g]
  have hyfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.y = ψ.y :=
    fun g => by rw [← Isogeny.conj_y, hfix g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (E.baseChange Ω) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (E.baseChange Ω) r₂ = a at hr₂
  change ratEmb (E.baseChange Ω) r₃ = b at hr₃
  have hab_fix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) a = a ∧ galFF E (g.restrictScalars F) b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add, map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX E _ ha) (galFF_mem_adjoin_genX E _ hb)
      ha hb e
  have h1 := isAlgebraic_coeffs (E := E) (r := r) (fun g => by rw [hr]; exact hxfix g)
  have h2 := isAlgebraic_coeffs (E := E) (r := r₂) (fun g => by rw [hr₂]; exact (hab_fix g).1)
  have h3 := isAlgebraic_coeffs (E := E) (r := r₃) (fun g => by rw [hr₃]; exact (hab_fix g).2)
  set S : Finset Ω := (r.num.coeffs ∪ r.denom.coeffs) ∪ (r₂.num.coeffs ∪ r₂.denom.coeffs) ∪
    (r₃.num.coeffs ∪ r₃.denom.coeffs) with hS
  have hSalg : ∀ c ∈ (S : Set Ω), _root_.IsIntegral F c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact (h1 c hc).isIntegral
      · exact (h2 c hc).isIntegral
    · exact (h3 c hc).isIntegral
  set F₁ := IntermediateField.adjoin F (S : Set Ω)
  haveI : FiniteDimensional F F₁ := IntermediateField.finiteDimensional_adjoin hSalg
  obtain ⟨n₁, hn₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₁, hd₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₂, hn₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₂, hd₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₃, hn₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₃, hd₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.denom)
    (fun c hc => by simp [hS, hc])
  set σ₁ := algebraMap F₁ Ω
  set C₁ := E.baseChange F₁
  have h := map_toAlgHom_baseChange F₁ E
  have h' := map_toAlgHom_baseChange F₁ E'
  set ψ₁ := ψ.congr h.symm h'.symm
  set X₁ := genX C₁
  set x₁ : C₁.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : C₁.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY C₁
  have hrat : ∀ (s : RatFunc Ω) (p q : Polynomial F₁), p.map σ₁ = s.num → q.map σ₁ = s.denom →
      ffMap σ₁ C₁ (aeval X₁ p / aeval X₁ q) = ffCongr h.symm (ratEmb (E.baseChange Ω) s) := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, map_div₀, ffCongr_aeval, ffCongr_aeval, ffMap_aeval, ffMap_aeval,
      ffMap_genX, hp, hq]
  have hx₁ : ffMap σ₁ C₁ x₁ = ψ₁.x := by
    rw [Isogeny.congr_alt, ← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap σ₁ C₁ y₁ = ψ₁.y := by
    rw [Isogeny.congr_y, hab, map_add, map_mul, ← hr₂, ← hr₃, map_add, map_mul,
      hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃, ffMap_genY, ffCongr_genY]
  refine ⟨F₁, inferInstance, Isogeny.ofMap σ₁ ψ₁ x₁ y₁ hx₁ hy₁, h, h', ?_⟩
  rw [Isogeny.mapOf, Isogeny.map_ofMap]
  exact Isogeny.congr_congr h.symm h'.symm ψ

/- English proof (translation)
Take `⟨F₁, hfin, rest⟩` from `ψ.exists_finiteDimensional_mapOf_eq`. Conclude with `⟨F₁, NumberField.of_module_finite F F₁, rest⟩`.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_numberField_mapOf_eq [NumberField F]
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, NumberField F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  obtain ⟨F₁, hfin, rest⟩ := ψ.exists_finiteDimensional_mapOf_eq
  exact ⟨F₁, NumberField.of_module_finite F F₁, rest⟩

end Descent

section OverF

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [DecidableEq Ω] in

/- English proof (translation)
Establish `e : (galFF E g).toRingHom.comp (bcEmb (F'` using `Ω) E).toRingHom = (bcEmb (F' := Ω) E).toRingHom := by`. Apply `ringHom_ext_functionField` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, AlgHom.commutes]`. Conclude with `galFF_algebraMap_base E g a`.

Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, bcEmb_genX]`. Conclude with `galFF_genX E g`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, bcEmb_genY]`. Conclude with `galFF_genY E g`. Conclude with `DFunLike.congr_fun e f`.
-/
theorem galFF_bcEmb (g : Ω ≃ₐ[F] Ω) (f : E.toAffine.FunctionField) :
    galFF E g (bcEmb (F' := Ω) E f) = bcEmb (F' := Ω) E f := by
  have e : (galFF E g).toRingHom.comp (bcEmb (F' := Ω) E).toRingHom =
      (bcEmb (F' := Ω) E).toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, AlgHom.commutes]
      exact galFF_algebraMap_base E g a
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genX]
      exact galFF_genX E g
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genY]
      exact galFF_genY E g
  exact DFunLike.congr_fun e f

/- English proof (translation)
The claim follows from `Isogeny.ext_xy (by rw [Isogeny.conj_alt_bis, isogBaseChange_alt, galFF_bcEmb]) (by rw [Isogeny.conj_y, isogBaseChange_y, galFF_bcEmb])`.
-/
theorem conj_isogBaseChange (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).conj g = isogBaseChange (F' := Ω) φ :=
  Isogeny.ext_xy (by rw [Isogeny.conj_alt_bis, isogBaseChange_alt, galFF_bcEmb])
    (by rw [Isogeny.conj_y, isogBaseChange_y, galFF_bcEmb])

/- English proof (translation)
Use `(isogBaseChange (F' := Ω) φ).pointMap_conj g R` as an intermediate fact. Rewrite `this` using `[conj_isogBaseChange]`. Then use the resulting hypothesis.
-/
theorem pointMap_isogBaseChange_galPointsHom [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E')
    (R : (E.baseChange Ω).toAffine.Point) :
    (isogBaseChange (F' := Ω) φ).pointMap (galPointsHom F Ω E g R) =
      galPointsHom F Ω E' g ((isogBaseChange (F' := Ω) φ).pointMap R) := by
  have := (isogBaseChange (F' := Ω) φ).pointMap_conj g R
  rwa [conj_isogBaseChange] at this

/- English proof (translation)
Use `set Q := (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P)`. Establish `hfix : ∀ g : Ω ≃ₐ[F] Ω, galPointsHom F Ω E' g Q = Q`. Introduce `g`. Rewrite using `[← pointMap_isogBaseChange_galPointsHom]`. Use `congr 1`.

Conclude with `map_constMap E (g : Ω →ₐ[F] Ω) P`. Consider the cases of `hQ : Q with`. Consider the case `zero => exact ⟨0, (map_zero (constMap E' Ω)).symm⟩`. Consider the case `some u v h`. Rewrite `hfix` using `[hQ]`.

Establish `key : ∀ g : Ω ≃ₐ[F] Ω, g u = u ∧ g v = v`. Introduce `g`. Use `hfix g` as an intermediate fact. Take `⟨h', e⟩` from `galPointsHom_some F Ω E' g h`. Rewrite `this` using `[e]`.

Conclude with `⟨(Point.some.inj this).1, (Point.some.inj this).2⟩`. Establish `hu : u ∈ (⊥ : IntermediateField F Ω)` using `mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).1`. Establish `hv : v ∈ (⊥ : IntermediateField F Ω)` using `mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).2`. Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.mp hu`. Take `⟨b, rfl⟩` from `IntermediateField.mem_bot.mp hv`.

Establish `hab : E'.toAffine.Nonsingular a b` using `(E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F Ω) (algebraMap F Ω).injective a b).mp h`. Conclude with `⟨.some a b hab, rfl⟩`.
-/
theorem exists_pointMap_isogBaseChange_eq [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    ∃ P' : E'.toAffine.Point,
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) = constMap E' Ω P' := by
  set Q := (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P)
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, galPointsHom F Ω E' g Q = Q := by
    intro g
    rw [← pointMap_isogBaseChange_galPointsHom]
    congr 1
    exact map_constMap E (g : Ω →ₐ[F] Ω) P
  cases hQ : Q with
  | zero => exact ⟨0, (map_zero (constMap E' Ω)).symm⟩
  | some u v h =>
    rw [hQ] at hfix
    have key : ∀ g : Ω ≃ₐ[F] Ω, g u = u ∧ g v = v := by
      intro g
      have := hfix g
      obtain ⟨h', e⟩ := galPointsHom_some F Ω E' g h
      rw [e] at this
      exact ⟨(Point.some.inj this).1, (Point.some.inj this).2⟩
    have hu : u ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).1
    have hv : v ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).2
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hu
    obtain ⟨b, rfl⟩ := IntermediateField.mem_bot.mp hv
    have hab : E'.toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F Ω) (algebraMap F Ω).injective a b).mp h
    exact ⟨.some a b hab, rfl⟩

variable (Ω) in

noncomputable def pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E') :
    E.toAffine.Point →+ E'.toAffine.Point :=
  AddMonoidHom.mk' (fun P => (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose)
    (fun P₁ P₂ => by
      apply constMap_injective E' Ω
      have e₃ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ (P₁ + P₂)).choose_spec
      have e₁ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₁).choose_spec
      have e₂ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₂).choose_spec
      rw [map_add (constMap E' Ω), ← e₃, ← e₁, ← e₂, map_add (constMap E Ω),
        Isogeny.pointMap_add])

/- English proof (translation)
The claim follows from `(exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose_spec.symm`.
-/
theorem constMap_pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    constMap E' Ω (pointHomOver Ω φ P) =
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) :=
  (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose_spec.symm

omit [DecidableEq Ω] in

/- English proof (translation)
The claim follows from `Isogeny.ext_xy ((ffMap σ E).injective (by rw [← Isogeny.map_x, h, Isogeny.map_x])) ((ffMap σ E).injective (by rw [← Isogeny.map_y, h, Isogeny.map_y]))`.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_injective {F' : Type u} [Field F'] (σ : F →+* F')
    {φ ψ : Isogeny E E'} (h : φ.map σ = ψ.map σ) : φ = ψ :=
  Isogeny.ext_xy ((ffMap σ E).injective (by rw [← Isogeny.map_x, h, Isogeny.map_x]))
    ((ffMap σ E).injective (by rw [← Isogeny.map_y, h, Isogeny.map_y]))

end OverF

end GroundTheory.Global
