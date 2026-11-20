import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValQuot

/- English proof (translation)
Introduce `S _ π hV f' g'`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective f'`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective g'`. Establish `hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π}` using `fun x => ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩`. Take `⟨e₁, he1, h1f, h1π⟩` from `hV f π (hpi f)`.

Take `⟨e₂, he2, h2g, h2π⟩` from `hV g π (hpi g)`. Take `⟨a1, ha1⟩` from `Ideal.mem_span_singleton'.mp h1f`. Take `⟨b1, hb1⟩` from `Ideal.mem_span_singleton'.mp h1π`. Take `⟨a2, ha2⟩` from `Ideal.mem_span_singleton'.mp h2g`. Establish `he1' : e₁ * e₁ = e₁` using `he1`.

Establish `he2' : e₂ * e₂ = e₂` using `he2`. Take `⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂)` from `⟨_, rfl⟩`. Establish `hu2 : u * u = u` using `by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'`. Establish `he1u : e₁ * u = 0` using `by subst hu; linear_combination (-(1 - e₂)) * he1'`. Establish `huπ : u * π = (1 - e₂) * b1 * f` using `by subst hu; linear_combination (-(1 - e₂)) * hb1`.

Take `⟨e₃, he3, h3, h3'⟩` from `hV (u * f + (1 - u)) (u * g + (1 - u)) ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by`. Take the linear combination `((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩`. Establish `he3' : e₃ * e₃ = e₃` using `he3`. Take `⟨c3, hc3⟩` from `Ideal.mem_span_singleton'.mp h3`. Take `⟨d3, hd3⟩` from `Ideal.mem_span_singleton'.mp h3'`.

Use `⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) = Ideal.Quotient.mk _ (e₁ + u * e₃)`. Rewrite using `[← map_mul]`. Conclude with `congrArg (Ideal.Quotient.mk _) (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')`. Use `Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩`. Use `Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨-((1 - e₁) * a2), by`.

Take the linear combination `-(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩`.
-/
theorem valuation_comparable_quotient : ∀ {S : Type} [CommRing S] (π : S), Val π → Val0 (S ⧸ Ideal.span {π}) := by
  intro S _ π hV f' g'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  have hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π} := fun x =>
    ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩
  obtain ⟨e₁, he1, h1f, h1π⟩ := hV f π (hpi f)
  obtain ⟨e₂, he2, h2g, h2π⟩ := hV g π (hpi g)
  obtain ⟨a1, ha1⟩ := Ideal.mem_span_singleton'.mp h1f
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.mp h1π
  obtain ⟨a2, ha2⟩ := Ideal.mem_span_singleton'.mp h2g
  have he1' : e₁ * e₁ = e₁ := he1
  have he2' : e₂ * e₂ = e₂ := he2
  obtain ⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hu2 : u * u = u := by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'
  have he1u : e₁ * u = 0 := by subst hu; linear_combination (-(1 - e₂)) * he1'
  have huπ : u * π = (1 - e₂) * b1 * f := by subst hu; linear_combination (-(1 - e₂)) * hb1
  obtain ⟨e₃, he3, h3, h3'⟩ := hV (u * f + (1 - u)) (u * g + (1 - u))
    ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by
      linear_combination ((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩
  have he3' : e₃ * e₃ = e₃ := he3
  obtain ⟨c3, hc3⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨d3, hd3⟩ := Ideal.mem_span_singleton'.mp h3'
  refine ⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩
  · show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) =
      Ideal.Quotient.mk _ (e₁ + u * e₃)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _)
      (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-((1 - e₁) * a2), by
      linear_combination -(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩

end GlobalTheory.CompanionTheory.ValQuot
