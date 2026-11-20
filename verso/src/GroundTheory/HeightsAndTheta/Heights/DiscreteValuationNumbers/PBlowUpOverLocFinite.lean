import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Algebra

variable {L : Type*} [Field L]

/- English proof (translation)
Take `⟨y, hyI, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Use `Submodule.iSup_induction _ (motive := fun g => ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r) hg ?_ ⟨1, one_ne_zero, 0, by simp⟩ ?_` and prove the remaining obligations. Introduce `m g hg`. Establish `hy : algebraMap A L y ^ m ∈ (Submodule.map (Algebra.linearMap A L) I) ^ m` using `Submodule.pow_mem_pow _ (Submodule.mem_map_of_mem hyI) m`. Establish `hgy` using `(Submodule.mem_div_iff_forall_mul_mem.mp hg) _ hy`.

Establish `h1 : Submodule.map (Algebra.linearMap A L) I ≤ 1`. Rewrite using `[Submodule.one_eq_range]`. Conclude with `LinearMap.map_le_range`. Establish `hone : ∀ k : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ k ≤ 1`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact (pow_zero _).le`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `(mul_le_mul' ih h1).trans (mul_one _).le`.

Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hone m hgy)`. Use `⟨y ^ m, pow_ne_zero _ hy0, r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hr, mul_comm]`. Introduce and unpack `g₁ g₂ ⟨d₁, hd₁, r₁, h₁⟩ ⟨d₂, hd₂, r₂, h₂⟩`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, d₂ * r₁ + d₁ * r₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_mul, map_add, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_mem_of_mem_blowUpColon (A : Subring L) (I : Ideal A) (hI : I ≠ ⊥) {g : L}
    (hg : g ∈ blowUpColon L I) : ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := by
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.iSup_induction _ (motive := fun g => ∃ d : A, d ≠ 0 ∧ ∃ r : A,
    algebraMap A L d * g = algebraMap A L r) hg ?_ ⟨1, one_ne_zero, 0, by simp⟩ ?_
  · intro m g hg
    have hy : algebraMap A L y ^ m ∈ (Submodule.map (Algebra.linearMap A L) I) ^ m :=
      Submodule.pow_mem_pow _ (Submodule.mem_map_of_mem hyI) m
    have hgy := (Submodule.mem_div_iff_forall_mul_mem.mp hg) _ hy
    have h1 : Submodule.map (Algebra.linearMap A L) I ≤ 1 := by
      rw [Submodule.one_eq_range]
      exact LinearMap.map_le_range
    have hone : ∀ k : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => exact (pow_zero _).le
      | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul' ih h1).trans (mul_one _).le
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hone m hgy)
    refine ⟨y ^ m, pow_ne_zero _ hy0, r, ?_⟩
    rw [map_pow, hr, mul_comm]
  · rintro g₁ g₂ ⟨d₁, hd₁, r₁, h₁⟩ ⟨d₂, hd₂, r₂, h₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, d₂ * r₁ + d₁ * r₂, ?_⟩
    simp only [map_mul, map_add, ← h₁, ← h₂]
    ring

/- English proof (translation)
Set `_` to `(Subring.inclusion hAB).toAlgebra`. Set `Bs : Submodule A L` to `{ carrier := B add_mem' := fun h₁ h₂ => add_mem h₁ h₂ zero_mem' := zero_mem _ smul_mem' := fun r f hf => by`. Rewrite using `[Algebra.smul_def]`. Conclude with `mul_mem (hAB r.2) hf }`. Take `⟨s, hs⟩ : Bs.FG` from `hfg.of_le fun f hf => hle f hf`.

Establish `hsB : ∀ g ∈ s, ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r` using `fun g hg => exists_mul_mem_of_mem_blowUpColon A I hI (hle g (show g ∈ Bs from hs ▸ Submodule.subset_span hg))`. Use `choose! dg hdg0 rg hrg using hsB`. Establish `hd0 : (∏ g ∈ s, dg g) ≠ 0` using `Finset.prod_ne_zero_iff.mpr hdg0`. Set `T : Submodule A L` to `{ carrier := {g | ∃ r : A, algebraMap A L (∏ g ∈ s, dg g) * g = algebraMap A L r} add_mem' := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ => ⟨r₁ + r₂, by rw [map_add, ← h₁, ← h₂, mul_add]⟩ zero_mem' := ⟨0, by simp⟩ smul_mem' := fun c g ⟨r, hr⟩ => ⟨c * r, by`. Rewrite using `[Algebra.smul_def, map_mul, ← hr]`.

Use the proof step `ring⟩ }`. Establish `hBT : Bs ≤ T`. Rewrite using `[← hs, Submodule.span_le]`. Introduce `g hg`. Use `⟨(∏ g' ∈ s.erase g, dg g') * rg g, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← hrg g hg, ← Finset.prod_erase_mul s dg hg, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `φ : Bs →ₗ[A] L` to `(LinearMap.mulLeft A (algebraMap A L (∏ g ∈ s, dg g))).comp Bs.subtype`. Establish `hφ : Function.Injective φ` using `fun f₁ f₂ h => Subtype.ext (mul_left_cancel₀ (fun h0 => hd0 (Subtype.ext h0)) h)`. Establish `hφr : LinearMap.range φ ≤ LinearMap.range (Algebra.linearMap A L)`.

Introduce and unpack `_ ⟨f, rfl⟩`. Take `⟨r, hr⟩` from `hBT f.2`. Conclude with `⟨r, hr.symm⟩`. Establish `hinj : Function.Injective (Algebra.linearMap A L)` using `fun _ _ h => Subtype.ext h`. Establish `hle1 : Module.rank A Bs ≤ 1`.

Rewrite using `[← rank_range_of_injective φ hφ, ← Module.rank_self A, ← rank_range_of_injective _ hinj]`. Conclude with `Submodule.rank_mono hφr`. Set `ψ : A →ₗ[A] Bs` to `(Algebra.linearMap A L).codRestrict Bs fun r => hAB r.2`. Establish `hge1 : 1 ≤ Module.rank A Bs`. Rewrite using `[← Module.rank_self A]`.

Conclude with `LinearMap.rank_le_of_injective ψ fun x y h => hinj (show Algebra.linearMap A L x = Algebra.linearMap A L y from congrArg (fun z : Bs => (z : L)) h)`. Set `e : Bs ≃ₗ[A] B` to `{ toFun := fun f => ⟨f.1, f.2⟩ invFun := fun f => ⟨f.1, f.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `: Module.Finite A Bs` using `Module.Finite.iff_fg.mpr ⟨s, hs⟩`. Use `⟨Module.Finite.equiv e, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.finrank_eq]`.

Conclude with `Module.finrank_eq_of_rank_eq (le_antisymm hle1 (by exact_mod_cast hge1))`.
-/
theorem finite_finrank_one_of_le_blowUpColon (A B : Subring L) [IsNoetherianRing A] (hAB : A ≤ B)
    (I : Ideal A) (hI : I ≠ ⊥) (hfg : (blowUpColon L I).FG) (hle : ∀ f ∈ B, f ∈ blowUpColon L I) :
    letI := (Subring.inclusion hAB).toAlgebra
    Module.Finite A B ∧ Module.finrank A B = 1 := by
  classical
  let _ := (Subring.inclusion hAB).toAlgebra

  let Bs : Submodule A L :=
    { carrier := B
      add_mem' := fun h₁ h₂ => add_mem h₁ h₂
      zero_mem' := zero_mem _
      smul_mem' := fun r f hf => by
        rw [Algebra.smul_def]
        exact mul_mem (hAB r.2) hf }
  obtain ⟨s, hs⟩ : Bs.FG := hfg.of_le fun f hf => hle f hf

  have hsB : ∀ g ∈ s, ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := fun g hg =>
    exists_mul_mem_of_mem_blowUpColon A I hI (hle g (show g ∈ Bs from hs ▸ Submodule.subset_span hg))
  choose! dg hdg0 rg hrg using hsB
  have hd0 : (∏ g ∈ s, dg g) ≠ 0 := Finset.prod_ne_zero_iff.mpr hdg0
  let T : Submodule A L :=
    { carrier := {g | ∃ r : A, algebraMap A L (∏ g ∈ s, dg g) * g = algebraMap A L r}
      add_mem' := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ => ⟨r₁ + r₂, by rw [map_add, ← h₁, ← h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c g ⟨r, hr⟩ => ⟨c * r, by
        rw [Algebra.smul_def, map_mul, ← hr]
        ring⟩ }
  have hBT : Bs ≤ T := by
    rw [← hs, Submodule.span_le]
    intro g hg
    refine ⟨(∏ g' ∈ s.erase g, dg g') * rg g, ?_⟩
    rw [map_mul, ← hrg g hg, ← Finset.prod_erase_mul s dg hg, map_mul]
    ring

  let φ : Bs →ₗ[A] L := (LinearMap.mulLeft A (algebraMap A L (∏ g ∈ s, dg g))).comp Bs.subtype
  have hφ : Function.Injective φ := fun f₁ f₂ h => Subtype.ext
    (mul_left_cancel₀ (fun h0 => hd0 (Subtype.ext h0)) h)
  have hφr : LinearMap.range φ ≤ LinearMap.range (Algebra.linearMap A L) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨r, hr⟩ := hBT f.2
    exact ⟨r, hr.symm⟩
  have hinj : Function.Injective (Algebra.linearMap A L) := fun _ _ h => Subtype.ext h
  have hle1 : Module.rank A Bs ≤ 1 := by
    rw [← rank_range_of_injective φ hφ, ← Module.rank_self A,
      ← rank_range_of_injective _ hinj]
    exact Submodule.rank_mono hφr
  let ψ : A →ₗ[A] Bs := (Algebra.linearMap A L).codRestrict Bs fun r => hAB r.2
  have hge1 : 1 ≤ Module.rank A Bs := by
    rw [← Module.rank_self A]
    exact LinearMap.rank_le_of_injective ψ fun x y h =>
      hinj (show Algebra.linearMap A L x = Algebra.linearMap A L y from congrArg (fun z : Bs => (z : L)) h)

  let e : Bs ≃ₗ[A] B :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite A Bs := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle1 (by exact_mod_cast hge1))

end Algebra

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ J _ P n hP N u hu ⟨j₀, hj₀⟩ c x hx hxP W hW hWrel`. Use `hP.multiProj.isPrime` as an intermediate fact. Take `⟨hL, hN, hD⟩` from `hloc O K ι P hP.multiProj c x hx hxP W hW hWrel`. Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`.

Establish `he : ∀ f, f ∉ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0` using `fun f hf h0 => hf (by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P)) (h0.trans (map_zero _).symm))`. Establish `he0 : ∀ f, f ∈ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) = 0` using `fun f hf => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]`.

Take `⟨i, hi⟩` from `powMonomial_not_mem hWp hWrel N`. Establish `hh0` using `he (powMonomial N i) fun hm => hi (hPW hm)`. Set `a : J → homLocRing P W` to `fun k => ⟨algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i)), Subring.subset_closure ⟨N, u k, powMonomial N i, hu k, isMultiHomog_powMonomial N i …`. Establish `hI : Ideal.span (Set.range a) ≠ ⊥`. Introduce `hb`.

Establish `h1 : a j₀ ∈ Ideal.span (Set.range a)` using `Ideal.subset_span ⟨j₀, rfl⟩`. Rewrite `h1` using `[hb, Ideal.mem_bot]`. Conclude with `div_ne_zero (he _ hj₀) hh0 (congrArg Subtype.val h1)`. Establish `hle : ∀ f ∈ blowUpOverLoc P W u, f ∈ blowUpColon (FractionRing (MRing ι O ⧸ P)) (Ideal.span (Set.range a))`. Introduce `f hf`.

Use `hcolon (homLocRing P W) _ J a f fun k hk => ?_` and prove the remaining obligations. Establish `huk : u k ∉ P` using `fun hm => hk (by show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / _ = 0`. Rewrite using `[he0 _ hm, zero_div])`. Use `(Subring.closure_le (t := (Algebra.adjoin (homLocRing P W) _).toSubring)).mpr (Set.union_subset ?_ ?_) (hchart O K ι J P W hP.multiProj.multiHomog hWp hPW hWrel N u hu k huk hf)` and prove the remaining obligations. Introduce `z hz`.

Conclude with `Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : homLocRing P W)`. Introduce and unpack `_ ⟨l, rfl⟩`. Use `Algebra.subset_adjoin ⟨l, ?_⟩` and prove the remaining obligations. Conclude with `div_div_div_cancel_right₀ hh0 (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u l))) (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)))`. Use `hN` as an intermediate fact.

Conclude with `finite_finrank_one_of_le_blowUpColon (homLocRing P W) (blowUpOverLoc P W u) (homLocRing_le_blowUpOverLoc P W u) _ hI (hfin (homLocRing P W) _ (fun _ _ h => Subtype.ext h) hD _ hI) hle`.
-/
theorem BlowUpOverLocFinite.proof (hloc : HomLocRingLocal.Statement.{u})
    (hchart : BlowUpOverLocInChart.Statement.{u}) (hcolon : ChartsInColon.Statement.{u})
    (hfin : BlowUpColonFinite.Statement.{u}) : BlowUpOverLocFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu ⟨j₀, hj₀⟩ c x hx hxP W hW hWrel
  have := hP.multiProj.isPrime
  obtain ⟨hL, hN, hD⟩ := hloc O K ι P hP.multiProj c x hx hxP W hW hWrel
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have he : ∀ f, f ∉ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) ≠ 0 := fun f hf h0 => hf (by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P)) (h0.trans (map_zero _).symm))
  have he0 : ∀ f, f ∈ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) = 0 := fun f hf => by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel N
  have hh0 := he (powMonomial N i) fun hm => hi (hPW hm)
  let a : J → homLocRing P W := fun k =>
    ⟨algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i)),
      Subring.subset_closure ⟨N, u k, powMonomial N i, hu k, isMultiHomog_powMonomial N i, hi, rfl⟩⟩
  have hI : Ideal.span (Set.range a) ≠ ⊥ := by
    intro hb
    have h1 : a j₀ ∈ Ideal.span (Set.range a) := Ideal.subset_span ⟨j₀, rfl⟩
    rw [hb, Ideal.mem_bot] at h1
    exact div_ne_zero (he _ hj₀) hh0 (congrArg Subtype.val h1)

  have hle : ∀ f ∈ blowUpOverLoc P W u, f ∈ blowUpColon (FractionRing (MRing ι O ⧸ P)) (Ideal.span (Set.range a)) := by
    intro f hf
    refine hcolon (homLocRing P W) _ J a f fun k hk => ?_
    have huk : u k ∉ P := fun hm => hk (by
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / _ = 0
      rw [he0 _ hm, zero_div])
    refine (Subring.closure_le (t := (Algebra.adjoin (homLocRing P W) _).toSubring)).mpr
      (Set.union_subset ?_ ?_) (hchart O K ι J P W hP.multiProj.multiHomog hWp hPW hWrel N u hu k huk hf)
    · intro z hz
      exact Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : homLocRing P W)
    · rintro _ ⟨l, rfl⟩
      refine Algebra.subset_adjoin ⟨l, ?_⟩
      exact div_div_div_cancel_right₀ hh0
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u l)))
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)))
  have := hN
  exact finite_finrank_one_of_le_blowUpColon (homLocRing P W) (blowUpOverLoc P W u)
    (homLocRing_le_blowUpOverLoc P W u) _ hI
    (hfin (homLocRing P W) _ (fun _ _ h => Subtype.ext h) hD _ hI) hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
