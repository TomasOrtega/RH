import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient]`. Establish `hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (R` using `R) (Ideal.span {s}) := fun P => by`. Simplify using `only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]`. Conclude with `Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩) (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))`.
-/
private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

/- English proof (translation)
Use `set T := Algebra.adjoin D (F : Set E)`. Establish `: Algebra.IsIntegral D T` using `⟨fun x => (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩`. Establish `: Algebra.FiniteType D T` using `(Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)`. Establish `: Algebra.FiniteType ℤ T` using `Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance`. Establish `hsT : algebraMap D T s = 0` using `Subtype.ext (by simpa using hsE)`.

Establish `h1 : ringKrullDim T < d` using `(ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt`. Establish `h2 : IsUnit (q : T)` using `by simpa using hqD.map (algebraMap D T)`. Conclude with `hlow T h2 h1`.
-/
private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE`. Establish `hquot` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)`. Establish `hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d`. Establish `h` using `hquot.trans hdD`. Generalize the expression as in `ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢`.

Consider the cases of `a using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe a`. Establish `h' : a + 1 ≤ (d : ℕ∞)` using `by exact_mod_cast h`. Establish `ha : a ≠ ⊤` using `ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')`.

Conclude with `(ENat.add_one_le_iff ha).mp h'` after adjusting the coercions. Conclude with `GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ) (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx) (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩) (fun F => by`. Establish `h` using `hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))`. Rewrite `h` using `[map_natCast]`. Conclude with `h)`.

Use the proof step `(fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)`.
-/
theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
