import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnitsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.KerDet

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
The claim follows from `finPartI_eq_self fun _ => rfl`.
-/
theorem finPartI_localIdele (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finPartI L (localIdele L v x) = localIdele L v x :=
  finPartI_eq_self fun _ => rfl

/- English proof (translation)
Establish `h1` using `h.1 v k`. Unfold `HChar.resFin at h1`. Rewrite `h1` using `[MonoidHom.finsetProd_apply]`. Unfold `locF`. Rewrite using `[map_prod, map_prod, ← h1]`.

Conclude with `Finset.prod_congr rfl fun Q _ => congrArg χ.1 (finPartI_localIdele Q _)`.
-/
theorem map_finPartI_locF {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (locF F v k)) = 1 := by
  have h1 := h.1 v k
  unfold HChar.resFin at h1
  rw [MonoidHom.finsetProd_apply] at h1
  unfold locF
  rw [map_prod, map_prod, ← h1]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (finPartI_localIdele Q _)

/- English proof (translation)
Break down `eq_or_ne γ 0 with rfl | h0` into its components or cases. Conclude with `zero_le`. Rewrite `h` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[← WithZero.exp_log h0, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

open Classical in

/- English proof (translation)
Introduce `R H`. Use `⟨KDq_empty H ▸ isOpen_KDq H ∅, fun w y => KDq_le_KD H ∅ (infIdele_mem_KDq H ∅ w y), fun k => KDq_le_KD H ∅ (diag_upF_mem_KDq H ∅ k), fun χ hT hta hu => (Subgroup.closure_le _).2 ?_⟩` and prove the remaining obligations. Introduce and unpack `a (ha | ⟨v, k, rfl⟩)`. Use `GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_` and prove the remaining obligations. Establish `hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v` using `hx`.

Establish `hxu : IsUnitAt v x`. Unfold `IsUnitAt`. Rewrite using `[hx']`. Conclude with `ha.1 v`. Distinguish the cases in `hv : ∃ k, OverP H (H.g k) v`.

Take `⟨k, hk⟩` from `hv`. Use `hta v x hxu (le_exp_neg_one ?_)` and prove the remaining obligations. Rewrite using `[hx']`. Conclude with `ha.2 k v hk`. Conclude with `hu v (not_exists.1 hv) x hxu`.

Conclude with `map_finPartI_locF hT v k`.
-/
theorem kernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (Ideles H.E)) ∧ (∀ w y, infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, diagUnits H.E (upF H.F k) ∈ KD H) ∧ ∀ χ : HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  intro R H
  refine ⟨KDq_empty H ▸ isOpen_KDq H ∅, fun w y => KDq_le_KD H ∅ (infIdele_mem_KDq H ∅ w y),
    fun k => KDq_le_KD H ∅ (diag_upF_mem_KDq H ∅ k), fun χ hT hta hu => (Subgroup.closure_le _).2 ?_⟩
  rintro a (ha | ⟨v, k, rfl⟩)
  · refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_
    have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
    have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact ha.1 v
    by_cases hv : ∃ k, OverP H (H.g k) v
    · obtain ⟨k, hk⟩ := hv
      refine hta v x hxu (le_exp_neg_one ?_)
      rw [hx']
      exact ha.2 k v hk
    · exact hu v (not_exists.1 hv) x hxu
  · exact map_finPartI_locF hT v k

end GlobalTheory.Mem.KerDet
