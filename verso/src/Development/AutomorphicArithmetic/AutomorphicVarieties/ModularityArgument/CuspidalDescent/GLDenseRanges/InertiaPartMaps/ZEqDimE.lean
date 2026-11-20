import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AutomorphicTensorInductionOfLocalPlaces

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

open private au_isTeich from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

/- English proof (translation)
Simplify using `[ePart, opE]`.
-/
private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0`. Use extensionality with `x`. Conclude with `(s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)`. Establish `h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`. Establish `h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal`. Rewrite `h2` using `[← hw]`. Establish `h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal` using `h2`.

Rewrite `h4` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)})` using `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)`. Establish `hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L)`. Rewrite using `[Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]`. Simplify using `[Int.natAbs_pow]`.

Rewrite `hd` using `[hn]`. Take `⟨e, -, he⟩` from `(Nat.dvd_prime_pow s.p_prime).1 hd`. Establish `hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e` using `(resCard_eq_normV _).trans he`. Introduce `h`. Rewrite `h` using `[hq]`.

Conclude with `s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm`.
-/
private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e := (resCard_eq_normV _).trans he
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4`. Take `⟨a, j, D₀, hE, hD₀, hdim⟩` from `hLoc ((s.w s.v0).adicCompletion L) n`. Use `⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩` and prove the remaining obligations. Introduce `Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'`. Take `⟨a₀, ha⟩` from `hCount hP hM hC l L Ω s n hn V hV hn4 ι lam`.

Take `⟨t, ht⟩` from `au_isTeich c r`. Take `⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F` from `L) (s.A u) →* ℂˣ, IsType (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧ ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g := ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHo …`. Establish `key : ∀ D : ℕ, IsDimE (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D → ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧ (∀ (u : s.St) rc, IsRec (s.hw u) rc → IsTypeWD (s.hw u) (χ u) …`. Introduce and unpack `_ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩`. Take `⟨e, he⟩` from `hs.alg`.

Take `⟨π, σ, C, h1, h2, h3, h4, h5⟩` from `ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall`. Use `haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) := haveI := hs.fin K c0 le_rfl Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))`. Establish `hb` using `fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'`. Establish `h0` using `h5 0 0 (by simp)`. Establish `hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0` using `fun hf => hz (Submodule.finrank_eq_zero.1 hf)`.

Rewrite `h0` using `[show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq]`. Establish `hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0` using `h0 ▸ Nat.cast_ne_zero.2 hz0`. Establish `ha₀ : (a₀ : Cardinal) ≠ 0` using `left_ne_zero_of_mul hne`. Establish `hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0` using `left_ne_zero_of_mul (right_ne_zero_of_mul hne)`. Establish `hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥` using `fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)`.

Establish `hd` using `hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf`. Establish `hD` using `h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp`. Rewrite `hD` using `[hb, hd]`. Use `⟨π, σ, C, h1, fun u rc hrc => partUR2Type l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩` and prove the remaining obligations. Use `Nat.one_le_iff_ne_zero.2 fun h0' => ?_` and prove the remaining obligations.

Rewrite `hD` using `[h0', Nat.cast_zero]`. Conclude with `mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm`. Take `⟨π, σ, C, a1, a3, a5, a6⟩` from `key D h`. Take `⟨π', σ', C', b1, b3, b5, -⟩` from `key D' h'`. Establish `hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀)` using `hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C' (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))`.

Rewrite `a5` using `[hr, ← b5]`. Conclude with `⟨a6, Nat.cast_injective (R := Cardinal) a5⟩`.
-/
theorem zEqDimE : CountE → ResEq2 → InvEq1 → InvBox → LocE → KirCusp → ZEqDimE := by
  intro hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4
  obtain ⟨a, j, D₀, hE, hD₀, hdim⟩ := hLoc ((s.w s.v0).adicCompletion L) n
  refine ⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩
  intro Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'
  obtain ⟨a₀, ha⟩ := hCount hP hM hC l L Ω s n hn V hV hn4 ι lam
  obtain ⟨t, ht⟩ := au_isTeich c r
  obtain ⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, IsType (fun u : s.St => s.hw u)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧
      ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g :=
    ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
      ((t i).comp (V.pr.comp (Weil (s.hw u)).subtype)), fun _ => rfl⟩⟩
  have key : ∀ D : ℕ, IsDimE (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D →
      ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
        (∀ (u : s.St) rc, IsRec (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (C.u u)))) ∧
        (D : Cardinal) = a₀ * (Module.rank ℂ (cInv1 C ι τ₀) * D₀) ∧ 1 ≤ D := by
    rintro _ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩
    obtain ⟨e, he⟩ := hs.alg
    obtain ⟨π, σ, C, h1, h2, h3, h4, h5⟩ := ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall
    haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) :=
      haveI := hs.fin K c0 le_rfl
      Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0)
        (inf_le_left.trans (iSup_le fun _ => inf_le_left))
    have hb := fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'
    have h0 := h5 0 0 (by simp)
    have hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0 :=
      fun hf => hz (Submodule.finrank_eq_zero.1 hf)
    rw [show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq] at h0
    have hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0 :=
      h0 ▸ Nat.cast_ne_zero.2 hz0
    have ha₀ : (a₀ : Cardinal) ≠ 0 := left_ne_zero_of_mul hne
    have hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥ := fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)
    have hd := hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf
    have hD := h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp
    rw [hb, hd] at hD
    refine ⟨π, σ, C, h1, fun u rc hrc =>
      partUR2Type l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩
    refine Nat.one_le_iff_ne_zero.2 fun h0' => ?_
    rw [h0', Nat.cast_zero] at hD
    exact mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm
  obtain ⟨π, σ, C, a1, a3, a5, a6⟩ := key D h
  obtain ⟨π', σ', C', b1, b3, b5, -⟩ := key D' h'
  have hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀) :=
    hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C'
      (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))
  rw [hr, ← b5] at a5
  exact ⟨a6, Nat.cast_injective (R := Cardinal) a5⟩

end UpperTheory.V.Z.Desc.V0
