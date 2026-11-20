import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftIdempotentAdicComplete

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompMod

/- English proof (translation)
Take `⟨c', hc'⟩` from `Ideal.mem_span_singleton.1 h`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c'`. Rewrite `hc'` using `[← map_mul]`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc')`. Conclude with `⟨c, d, by linear_combination hd⟩`.
-/
theorem exists_eq_add_of_mem_span_quot {S : Type} [CommRing S] (ϖ x y : S)
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) x ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) y}) :
    ∃ c d : S, x = y * c + ϖ ^ 2 * d := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul] at hc'
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc')
  exact ⟨c, d, by linear_combination hd⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective f`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective g`. Take `⟨ε, hε, h1, h2⟩` from `h0 (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)`. Take `⟨e, ⟨he, rfl⟩, -⟩` from `IdemLift.existsUnique_idempotent_lift ϖ 2 two_ne_zero ε hε`. Rewrite `h1` using `[← map_mul]`.

Establish `h2' : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 - e) * b) ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) a}`. Simplify `h2` using `[map_mul, map_sub, map_one]`. Take `⟨c, d, hcd⟩` from `exists_eq_add_of_mem_span_quot ϖ _ _ h1`. Take `⟨c', d', hcd'⟩` from `exists_eq_add_of_mem_span_quot ϖ _ _ h2'`. Establish `key : ∀ t : S, IsIdempotentElem t → t ∈ P → Ideal.Quotient.mk (compI P) t = 0` using `fun t ht htP => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ht, htP⟩)`.

Distinguish the cases in `heP : e ∈ P`. Use `right`. Establish `hz` using `key e he heP`. Establish `hb` using `congrArg (Ideal.Quotient.mk (compI P)) hcd'`. Simplify using `only [map_mul, map_add, map_sub, map_one, map_pow, hz, sub_zero, one_mul] at hb`.

Rewrite using `[hb]`. Conclude with `Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c', Ideal.Quotient.mk _ d', by ring⟩`. Use `left`. Establish `hmul : e * (1 - e) ∈ P`. Establish `: e * (1 - e) = 0`.

Establish `he' : e * e = e` using `he`. Take the linear combination `-he'`. Rewrite using `[this]`. Conclude with `P.zero_mem`. Establish `h1e : 1 - e ∈ P` using `(hP.mem_or_mem hmul).resolve_left heP`.

Establish `hz` using `key (1 - e) he.one_sub h1e`. Establish `hz' : Ideal.Quotient.mk (compI P) e = 1`. Rewrite `hz` using `[map_sub, map_one]`. Conclude with `(sub_eq_zero.1 hz).symm`. Establish `ha` using `congrArg (Ideal.Quotient.mk (compI P)) hcd`.

Simplify using `only [map_mul, map_add, map_pow, hz', one_mul] at ha`. Rewrite using `[ha]`. Conclude with `Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d, by ring⟩`.
-/
theorem mem_span_or_mem_span {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : Val0 (S ⧸ Ideal.span {ϖ ^ 2}))
    (P : Ideal S) (hP : P.IsPrime) (f g : S ⧸ compI P) :
    f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨
      g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨ε, hε, h1, h2⟩ := h0 (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)
  obtain ⟨e, ⟨he, rfl⟩, -⟩ :=
    IdemLift.existsUnique_idempotent_lift ϖ 2 two_ne_zero ε hε
  rw [← map_mul] at h1
  have h2' : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 - e) * b) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) a} := by
    simpa [map_mul, map_sub, map_one] using h2
  obtain ⟨c, d, hcd⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h1
  obtain ⟨c', d', hcd'⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h2'
  have key : ∀ t : S, IsIdempotentElem t → t ∈ P →
      Ideal.Quotient.mk (compI P) t = 0 := fun t ht htP =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ht, htP⟩)
  by_cases heP : e ∈ P
  · right
    have hz := key e he heP
    have hb := congrArg (Ideal.Quotient.mk (compI P)) hcd'
    simp only [map_mul, map_add, map_sub, map_one, map_pow, hz, sub_zero, one_mul] at hb
    rw [hb]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c', Ideal.Quotient.mk _ d', by ring⟩
  · left
    have hmul : e * (1 - e) ∈ P := by
      have : e * (1 - e) = 0 := by
        have he' : e * e = e := he
        linear_combination -he'
      rw [this]
      exact P.zero_mem
    have h1e : 1 - e ∈ P := (hP.mem_or_mem hmul).resolve_left heP
    have hz := key (1 - e) he.one_sub h1e
    have hz' : Ideal.Quotient.mk (compI P) e = 1 := by
      rw [map_sub, map_one] at hz
      exact (sub_eq_zero.1 hz).symm
    have ha := congrArg (Ideal.Quotient.mk (compI P)) hcd
    simp only [map_mul, map_add, map_pow, hz', one_mul] at ha
    rw [ha]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d, by ring⟩

end GlobalTheory.CompanionTheory.CompMod
