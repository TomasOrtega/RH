import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.WeilUp

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω}

/- English proof (translation)
Use `haveI := v'.isMaximal`. Use `letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _`. Use `haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot`. Take `⟨u, hu⟩` from `IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)`. Establish `hord : orderOf u = normV v' - 1`.

Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]`. Both sides reduce to the same expression. Rewrite using `[← hord, ← pow_eq_pow_iff_modEq]`. Take `⟨ζ, hζ⟩` from `Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)`. Establish `hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal`.

Rewrite using `[← h']`. Establish `e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) = (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)` using `by push_cast; simp [map_sub, map_pow]`. Rewrite using `[e]`. Conclude with `hc ζ`. Establish `h0` using `(Ideal.Quotient.eq_zero_iff_mem).mpr hmem`.

Rewrite `h0` using `[map_sub, map_pow, map_pow, hζ, sub_eq_zero]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_pow_eq_pow_val]`. Conclude with `h0.symm`.
-/
theorem modEq_of_cong {v' : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A v') {Q a b : ℕ}
    (hc : ∀ ζ : 𝓞 L, A.valuation ((algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)) < 1) :
    Q ^ a ≡ Q ^ b [MOD normV v' - 1] := by
  haveI := v'.isMaximal
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)
  have hord : orderOf u = normV v' - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]; rfl
  rw [← hord, ← pow_eq_pow_iff_modEq]
  obtain ⟨ζ, hζ⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)
  have hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal := by
    rw [← h']
    have e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) =
        (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a) := by
      push_cast; simp [map_sub, map_pow]
    rw [e]; exact hc ζ
  have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_pow, map_pow, hζ, sub_eq_zero] at h0
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  exact h0.symm

/- English proof (translation)
Establish `h1 : 1 ≤ q ^ n` using `Nat.one_le_pow _ _ (by omega)`. Establish `hd : q ^ f - 1 ∣ q ^ n - 1` using `(Nat.modEq_iff_dvd' h1).mp h.symm`. Establish `hg` using `Nat.pow_sub_one_gcd_pow_sub_one q f n`. Rewrite `hg` using `[Nat.gcd_eq_left hd]`. Establish `h2 : 1 ≤ q ^ f` using `Nat.one_le_pow _ _ (by omega)`.

Establish `h3 : 1 ≤ q ^ (f.gcd n)` using `Nat.one_le_pow _ _ (by omega)`. Establish `h4 : q ^ f = q ^ (f.gcd n)` using `by omega`. Establish `h5` using `Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4`. Rewrite using `[h5]`. Conclude with `Nat.gcd_dvd_right f n`.
-/
theorem dvd_of_modEq {q f n : ℕ} (hq : 1 < q) (h : q ^ n ≡ 1 [MOD q ^ f - 1]) : f ∣ n := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : q ^ f - 1 ∣ q ^ n - 1 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one q f n
  rw [Nat.gcd_eq_left hd] at hg
  have h2 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ (f.gcd n) := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ f = q ^ (f.gcd n) := by omega
  have h5 := Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4
  rw [h5]; exact Nat.gcd_dvd_right f n

/- English proof (translation)
Establish `e : σ = (g.restrictScalars K : G K Ω)` using `AlgEquiv.ext hg`. Substitute `e` using the available equality. Use `⟨hσ.1, fun x hx => ?_⟩` and prove the remaining obligations. Use `hσ.2 x hx` as an intermediate fact. Rewrite `this` using `[pow_mul, pow_mul]`.

Conclude with `this`.
-/
theorem actsAs_of_agree {q f a b : ℕ} {σ : G K Ω} {g : G L Ω} (hg : ∀ z : Ω, σ z = g z)
    (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) g a b := by
  have e : σ = (g.restrictScalars K : G K Ω) := AlgEquiv.ext hg
  subst e
  refine ⟨hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [pow_mul, pow_mul] at this
  exact this

end GlobalTheory.AboveL.WeilUp

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.WeilUp in

/- English proof (translation)
Introduce `K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg`. Take `⟨f, hf⟩` from `normV_eq_pow v v' (comap_eq_of_placeOver h h')`. Establish `hq : 1 < normV v` using `one_lt_normV v`. Establish `hcong : ∀ a b : ℕ, ActsAs A (normV v) (σ : G K Ω) a b → normV v ^ a ≡ normV v ^ b [MOD normV v ^ f - 1]`. Introduce `a b hab`.

Rewrite using `[← hf]`. Use `modEq_of_cong h' fun ζ => ?_` and prove the remaining obligations. Establish `hfix : (σ : G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L)`. Rewrite using `[hg]`. Conclude with `g.commutes _`.

Establish `hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1`. Rewrite using `[A.valuation_le_one_iff]`. Conclude with `mem_of_isIntegral_int A (ζ.2.algebraMap)`. Use `hab.2 _ hint` as an intermediate fact. Rewrite `this` using `[hfix]`. Then use the resulting hypothesis.

Use `set d := deg σ with hd`. Break down `le_total 0 d with hd0 | hd0` into its components or cases. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le hd0`. Establish `hact` using `actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)`. Establish `hdiv : f ∣ n` using `dvd_of_modEq hq (by simpa using hcong _ _ hact)`.

Take `⟨k, rfl⟩` from `hdiv`. Establish `hact'` using `actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)`. Conclude with `(mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩`. Take `⟨n, hn⟩` from `Int.exists_eq_neg_ofNat hd0`. Establish `hact` using `actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)`.

Establish `hdiv : f ∣ n` using `dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)`. Take `⟨k, rfl⟩` from `hdiv`. Establish `hact'` using `actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)`. Conclude with `(mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩`.
-/
theorem mem_weil_of_fix : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  have hq : 1 < normV v := one_lt_normV v

  have hcong : ∀ a b : ℕ, ActsAs A (normV v) (σ : G K Ω) a b →
      normV v ^ a ≡ normV v ^ b [MOD normV v ^ f - 1] := by
    intro a b hab
    rw [← hf]
    refine modEq_of_cong h' fun ζ => ?_
    have hfix : (σ : G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L) := by
      rw [hg]; exact g.commutes _
    have hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1 := by
      rw [A.valuation_le_one_iff]
      exact mem_of_isIntegral_int A (ζ.2.algebraMap)
    have := hab.2 _ hint
    rwa [hfix] at this
  set d := deg σ with hd
  rcases le_total 0 d with hd0 | hd0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd0
    have hact := actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using hcong _ _ hact)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd0
    have hact := actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩

end GlobalTheory.AboveL
