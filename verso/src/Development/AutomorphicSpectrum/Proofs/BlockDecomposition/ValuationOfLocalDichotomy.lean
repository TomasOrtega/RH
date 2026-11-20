import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

/- English proof (translation)
Introduce `S _ ϖ hD f g hfg`. Take `⟨N, hN⟩` from `hfg`. Set `Q : S → Prop` to `fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧ (e - d) * g ∈ Ideal.span {f}`. Establish `hQ1 : Q 1`. Apply `GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q` to reduce the goal to its premises.

Conclude with `⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩`. Introduce and unpack `e e' he he' ⟨d, hd, hde, hdf, hdg⟩`. Use `⟨d * e', hd.mul he', ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm d e', mul_assoc]`.

Conclude with `Ideal.mul_mem_left _ _ hdf`. Establish `h3 : (e * e' - d * e') * g = e' * ((e - d) * g)` using `by ring`. Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_left _ _ hdg`. Introduce and unpack `e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩`.

Establish `hdd : d * d' = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : d * e' = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : d' * e = 0`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨d + d', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (d + d') * (d + d') = d + d'`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[add_mul]`. Conclude with `Ideal.add_mem _ hdf hdf'`. Establish `h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g` using `by ring`. Rewrite using `[h3]`. Conclude with `Ideal.add_mem _ hdg hdg'`.

Introduce `m hm`. Establish `hprime` using `hm.isPrime`. Establish `hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈ Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g}`. Rewrite using `[← map_pow]`. Establish `h4` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN`.

Rewrite `h4` using `[Ideal.map_span, Set.image_pair]`. Then use the resulting hypothesis. Break down `hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'` into its components or cases. Take `⟨c, hc⟩` from `hgf`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]`. Take `⟨e, he, hem, hex⟩` from `(GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem`. Establish `hef : e * f = e * (g * a)`. Rewrite `hex` using `[mul_sub]`. Conclude with `sub_eq_zero.1 hex`.

Use `⟨e, he, hem, e, he, he.eq, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[hef]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))`. Take `⟨c, hc⟩` from `hfg'`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Establish `hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]`. Take `⟨e, he, hem, hex⟩` from `(GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem`. Establish `heg : e * g = e * (f * a)`. Rewrite `hex` using `[mul_sub]`.

Conclude with `sub_eq_zero.1 hex`. Use `⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero, heg]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))`. Take `⟨d, hd, -, hdf, hdg⟩` from `hQ1`.

Conclude with `⟨d, hd, hdf, hdg⟩`.
-/
theorem val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S),
    (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  intro S _ ϖ hD f g hfg
  obtain ⟨N, hN⟩ := hfg
  let Q : S → Prop := fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧
    (e - d) * g ∈ Ideal.span {f}
  have hQ1 : Q 1 := by
    apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q
    · exact ⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩
    · rintro e e' he he' ⟨d, hd, hde, hdf, hdg⟩
      refine ⟨d * e', hd.mul he', ?_, ?_, ?_⟩
      · calc d * e' * (e * e') = (d * e) * (e' * e') := by ring
          _ = d * e' := by rw [hde, he'.eq]
      · rw [mul_comm d e', mul_assoc]
        exact Ideal.mul_mem_left _ _ hdf
      · have h3 : (e * e' - d * e') * g = e' * ((e - d) * g) := by ring
        rw [h3]
        exact Ideal.mul_mem_left _ _ hdg
    · rintro e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩
      have hdd : d * d' = 0 := by
        calc d * d' = (d * e) * (d' * e') := by rw [hde, hde']
          _ = (d * d') * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h1 : d * e' = 0 := by
        calc d * e' = (d * e) * e' := by rw [hde]
          _ = d * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h2 : d' * e = 0 := by
        calc d' * e = (d' * e') * e := by rw [hde']
          _ = d' * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      refine ⟨d + d', ?_, ?_, ?_, ?_⟩
      · show (d + d') * (d + d') = d + d'
        calc (d + d') * (d + d') = d * d + d' * d' + 2 * (d * d') := by ring
          _ = d + d' := by rw [hd.eq, hd'.eq, hdd, mul_zero, add_zero]
      · calc (d + d') * (e + e') = d * e + d * e' + (d' * e + d' * e') := by ring
          _ = d + d' := by rw [hde, hde', h1, h2]; ring
      · rw [add_mul]
        exact Ideal.add_mem _ hdf hdf'
      · have h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g := by ring
        rw [h3]
        exact Ideal.add_mem _ hdg hdg'
    · intro m hm
      have hprime := hm.isPrime
      have hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈
          Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g} := by
        rw [← map_pow]
        have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN
        rwa [Ideal.map_span, Set.image_pair] at h4
      rcases hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'
      · obtain ⟨c, hc⟩ := hgf
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have hef : e * f = e * (g * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, e, he, he.eq, ?_, by simp⟩
        rw [hef]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
      · obtain ⟨c, hc⟩ := hfg'
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have heg : e * g = e * (f * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩
        rw [sub_zero, heg]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  obtain ⟨d, hd, -, hdf, hdg⟩ := hQ1
  exact ⟨d, hd, hdf, hdg⟩

end GlobalTheory.CompanionTheory.Idem
