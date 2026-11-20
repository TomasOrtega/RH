import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Introduce `R _ _ I hI P _`. Set `φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R` to `PrimeSpectrum.comap (Ideal.Quotient.mk I)`. Establish `hφ : StrictMono φ` using `RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective`. Set `z : PrimeSpectrum R` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q`.

Introduce `q`. Use `lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_` and prove the remaining obligations. Establish `hle : I ≤ (φ q).asIdeal`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I x ∈ q.asIdeal`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `q.asIdeal.zero_mem`. Rewrite `hle` using `[← h]`. Conclude with `le_bot_iff.mp hle`. Set `p : PrimeSpectrum (R ⧸ I)` to `⟨P, ‹_›⟩`.

Establish `h1 : P.height = Order.height p` using `PrimeSpectrum.height_eq_orderHeight p`. Establish `h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p)` using `PrimeSpectrum.height_eq_orderHeight (φ p)`. Establish `hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p }` using `⟨⟨RelSeries.singleton _ p, rfl⟩⟩`. Rewrite using `[h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]`. Introduce and unpack `⟨l, hl⟩`.

Set `l' : LTSeries (PrimeSpectrum R)` to `(l.map φ hφ).cons z (by simpa using hz l.head)`. Establish `hlast : l'.last = φ p` using `by simp [l', hl]`. Use `Order.length_le_height (p := l') hlast.le` as an intermediate fact. Simplify `this` using `[l']`.
-/
theorem QuotientHeightAddOne.proof : QuotientHeightAddOne.Statement := by
  intro R _ _ I hI P _
  let φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  let z : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩

  have hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q := by
    intro q
    refine lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_
    have hle : I ≤ (φ q).asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.asIdeal.zero_mem
    rw [← h] at hle
    exact le_bot_iff.mp hle
  let p : PrimeSpectrum (R ⧸ I) := ⟨P, ‹_›⟩
  have h1 : P.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p) :=
    PrimeSpectrum.height_eq_orderHeight (φ p)
  have hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p } :=
    ⟨⟨RelSeries.singleton _ p, rfl⟩⟩
  rw [h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]
  rintro ⟨l, hl⟩
  let l' : LTSeries (PrimeSpectrum R) :=
    (l.map φ hφ).cons z (by simpa using hz l.head)
  have hlast : l'.last = φ p := by simp [l', hl]
  have := Order.length_le_height (p := l') hlast.le
  simpa [l'] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
