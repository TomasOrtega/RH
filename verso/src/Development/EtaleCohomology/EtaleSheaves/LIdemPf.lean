import Development.EtaleCohomology.EtaleSheaves.HensIdemCut

noncomputable section
open Polynomial

namespace LateralTheory.E.LIdemPf

/- English proof (translation)
Introduce `A _ I B _ φ hJ b hb N g h hg hh hgh`. Use `set J := I.map φ with hJdef`. Set `π` to `Ideal.Quotient.mk J`. Set `ψ : A ⧸ I →+* B ⧸ J` to `Ideal.quotientMap J φ Ideal.le_comap_map`. Establish `hcomp : ψ.comp (Ideal.Quotient.mk I) = π.comp φ`.

Use extensionality with `a`. Simplify using `[ψ, π, Ideal.quotientMap_mk]`. Establish `key : ∀ p : A[X], π (p.eval₂ φ b) = (p.map (Ideal.Quotient.mk I)).eval₂ ψ (π b)`. Introduce `p`. Rewrite using `[Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]`.

Use `set G := g.eval₂ φ b with hGdef`. Use `set H := h.eval₂ φ b with hHdef`. Use `set e := π b with hedef`. Establish `hG : π G = e ^ N` using `by rw [key, hg]; simp`. Establish `hH : π H = (e - 1) ^ N` using `by rw [key, hh]; simp [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]`.

Establish `he : e * e = e`. Establish `: π (b * b - b) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hb`. Rewrite `this` using `[map_sub, map_mul]`. Conclude with `sub_eq_zero.mp this`. Establish `hcop : IsCoprime (e ^ N) ((e - 1) ^ N)` using `(show IsCoprime e (e - 1) from ⟨1, -1, by ring⟩).pow`.

Take `⟨u, v, huv⟩` from `hcop`. Take `⟨u', rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨v', rfl⟩` from `Ideal.Quotient.mk_surjective v`. Use `set s := u' * G + v' * H with hsdef`. Establish `hs : π s = π 1`.

Simplify using `only [hsdef, map_add, map_mul, hG, hH, map_one]`. Conclude with `huv`. Establish `hsJ : s - 1 ∈ Ideal.jacobson (⊥ : Ideal B)` using `hJ (Ideal.Quotient.eq.mp hs)`. Establish `hunit : IsUnit s`. Use `(Ideal.mem_jacobson_bot.mp hsJ) 1` as an intermediate fact.

Simplify using `using this`. Take `⟨w, hw⟩` from `hunit`. Establish `hsum : (↑w⁻¹ * u') * G + (↑w⁻¹ * v') * H = 1`. Establish `: (↑w⁻¹ : B) * s = 1` using `by rw [← hw]; exact Units.inv_mul w`. Rewrite `this` using `[hsdef]`.

Take the linear combination `this`. Use `⟨(↑w⁻¹ * u') * G, ?_, ?_⟩` and prove the remaining obligations. Use `show (↑w⁻¹ * u') * G * ((↑w⁻¹ * u') * G) = (↑w⁻¹ * u') * G`. Take the linear combination `((↑w⁻¹ * u') * G) * hsum - (↑w⁻¹ * u') * (↑w⁻¹ * v') * hgh`. Rewrite using `[← Ideal.Quotient.eq]`.

Express the relevant statement in the definitionally equal form `π ((↑w⁻¹ * u') * G) = e`. Establish `hsum'` using `congrArg π hsum`. Simplify using `only [map_add, map_mul, map_one, hG, hH] at hsum' ⊢`. Use `set α := π ↑w⁻¹ * π u'`. Use `set γ := π ↑w⁻¹ * π v'`.

Consider the cases of `N with`. Consider the case `zero`. Establish `h0 : (1 : B ⧸ J) = 0`. Use `congrArg π hgh` as an intermediate fact. Simplify `this` using `[map_mul, hG, hH]`.

Use `subsingleton_of_zero_eq_one h0.symm` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Consider the case `succ n`. Establish `hp : e ^ (n + 1) = e` using `IsIdempotentElem.pow_succ_eq n he`. Establish `h1 : e * (e - 1) ^ (n + 1) = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hsum'`, the goal using `[hp]`. Take the linear combination `e * hsum' - α * he - γ * h1`.
-/
theorem LIdem_of : LateralTheory.E.HensIdemCut.LIdem := by
  intro A _ I B _ φ hJ b hb N g h hg hh hgh
  set J := I.map φ with hJdef
  let π := Ideal.Quotient.mk J
  let ψ : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hcomp : ψ.comp (Ideal.Quotient.mk I) = π.comp φ := by
    ext a; simp [ψ, π, Ideal.quotientMap_mk]
  have key : ∀ p : A[X], π (p.eval₂ φ b) = (p.map (Ideal.Quotient.mk I)).eval₂ ψ (π b) := by
    intro p
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  set G := g.eval₂ φ b with hGdef
  set H := h.eval₂ φ b with hHdef
  set e := π b with hedef
  have hG : π G = e ^ N := by rw [key, hg]; simp
  have hH : π H = (e - 1) ^ N := by rw [key, hh]; simp [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]
  have he : e * e = e := by
    have : π (b * b - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_mul] at this
    exact sub_eq_zero.mp this
  have hcop : IsCoprime (e ^ N) ((e - 1) ^ N) :=
    (show IsCoprime e (e - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v', rfl⟩ := Ideal.Quotient.mk_surjective v
  set s := u' * G + v' * H with hsdef
  have hs : π s = π 1 := by
    simp only [hsdef, map_add, map_mul, hG, hH, map_one]
    exact huv
  have hsJ : s - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := hJ (Ideal.Quotient.eq.mp hs)
  have hunit : IsUnit s := by
    have := (Ideal.mem_jacobson_bot.mp hsJ) 1
    simpa using this
  obtain ⟨w, hw⟩ := hunit
  have hsum : (↑w⁻¹ * u') * G + (↑w⁻¹ * v') * H = 1 := by
    have : (↑w⁻¹ : B) * s = 1 := by rw [← hw]; exact Units.inv_mul w
    rw [hsdef] at this
    linear_combination this
  refine ⟨(↑w⁻¹ * u') * G, ?_, ?_⟩
  · show (↑w⁻¹ * u') * G * ((↑w⁻¹ * u') * G) = (↑w⁻¹ * u') * G
    linear_combination ((↑w⁻¹ * u') * G) * hsum - (↑w⁻¹ * u') * (↑w⁻¹ * v') * hgh
  · rw [← Ideal.Quotient.eq]
    change π ((↑w⁻¹ * u') * G) = e
    have hsum' := congrArg π hsum
    simp only [map_add, map_mul, map_one, hG, hH] at hsum' ⊢
    set α := π ↑w⁻¹ * π u'
    set γ := π ↑w⁻¹ * π v'
    cases N with
    | zero =>
      have h0 : (1 : B ⧸ J) = 0 := by
        have := congrArg π hgh
        simpa [map_mul, hG, hH] using this
      have := subsingleton_of_zero_eq_one h0.symm
      exact Subsingleton.elim _ _
    | succ n =>
      have hp : e ^ (n + 1) = e := IsIdempotentElem.pow_succ_eq n he
      have h1 : e * (e - 1) ^ (n + 1) = 0 := by
        calc e * (e - 1) ^ (n + 1) = (e * e - e) * (e - 1) ^ n := by ring
          _ = 0 := by rw [he, sub_self, zero_mul]
      rw [hp] at hsum' ⊢
      linear_combination e * hsum' - α * he - γ * h1

end LateralTheory.E.LIdemPf
