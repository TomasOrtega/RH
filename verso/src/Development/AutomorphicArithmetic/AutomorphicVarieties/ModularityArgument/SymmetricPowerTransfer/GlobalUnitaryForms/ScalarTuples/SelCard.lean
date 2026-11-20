import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit

open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

open Loc

/- English proof (translation)
Take `⟨u, s, hs, rfl⟩` from `h`. Take `⟨u', s', hs', rfl⟩` from `h'`. Conclude with `⟨u * u', s * s', mul_ne_zero hs hs', by simp only [Units.val_mul, map_mul]; ring⟩`.
-/
private theorem ev_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {x y : K} (h : EvenVal O x) (h' : EvenVal O y) :
    EvenVal O (x * y) := by
  obtain ⟨u, s, hs, rfl⟩ := h
  obtain ⟨u', s', hs', rfl⟩ := h'
  exact ⟨u * u', s * s', mul_ne_zero hs hs', by simp only [Units.val_mul, map_mul]; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, s, hs, by simp⟩`.
-/
private theorem ev_sq {O K : Type} [CommRing O] [Field K] [Algebra O K] {s : K} (hs : s ≠ 0) : EvenVal O (s ^ 2) :=
  ⟨1, s, hs, by simp⟩

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨u, s, hs, hx⟩` from `h`. Establish `hu : ∀ w : (Ov v)ˣ, Valued.v (algebraMap (Ov v) (Kv v) ↑w) = 1`. Introduce `w`. Establish `ha : Valued.v (algebraMap (Ov v) (Kv v) ↑w) ≤ 1` using `(w : Ov v).2`. Establish `hb : Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) ≤ 1` using `((w⁻¹ : (Ov v)ˣ) : Ov v).2`.

Establish `hm : Valued.v (algebraMap (Ov v) (Kv v) ↑w) * Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hv` using `congrArg Valued.v hx`.

Rewrite `hv` using `[map_mul, hu, one_mul, map_pow]`. Establish `hs0 : Valued.v s ≠ 0` using `(Valuation.ne_zero_iff _).mpr hs`. Take `⟨w, hw⟩` from `WithZero.ne_zero_iff_exists.mp hs0`. Establish `hva : Valued.v (cv v (a : F)) = v.valuation F (a : F)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : F)`. Establish `h2 : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = ((w ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[HeightOneSpectrum.valuationOfNeZero_eq, ← hva, hv, WithZero.coe_pow, hw]`. Establish `h3` using `WithZero.coe_inj.mp h2`. Use `⟨-Multiplicative.toAdd w, ?_⟩` and prove the remaining obligations. Simplify using `only [Kum.ordv, h3, toAdd_pow, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dvd_of_ev (v : Pl F) (a : Fˣ) (h : EvenVal (Ov v) (cv v (a : F))) : ((2 : ℕ) : ℤ) ∣ Kum.ordv v a := by
  obtain ⟨u, s, hs, hx⟩ := h
  have hu : ∀ w : (Ov v)ˣ, Valued.v (algebraMap (Ov v) (Kv v) ↑w) = 1 := by
    intro w
    have ha : Valued.v (algebraMap (Ov v) (Kv v) ↑w) ≤ 1 := (w : Ov v).2
    have hb : Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) ≤ 1 := ((w⁻¹ : (Ov v)ˣ) : Ov v).2
    have hm : Valued.v (algebraMap (Ov v) (Kv v) ↑w) * Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm ha ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
      _ ≤ Valued.v (algebraMap (Ov v) (Kv v) ↑w) * 1 := by gcongr
      _ = _ := mul_one _
  have hv := congrArg Valued.v hx
  rw [map_mul, hu, one_mul, map_pow] at hv
  have hs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs
  obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.mp hs0
  have hva : Valued.v (cv v (a : F)) = v.valuation F (a : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : F)
  have h2 : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((w ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ← hva, hv, WithZero.coe_pow, hw]
  have h3 := WithZero.coe_inj.mp h2
  refine ⟨-Multiplicative.toAdd w, ?_⟩
  simp only [Kum.ordv, h3, toAdd_pow, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Establish `hS : (S : Set (Pl F)).Finite` using `S.finite_toSet`. Establish `hc` using `Kum.cardSel F (S : Set (Pl F)) 2 two_ne_zero`. Establish `hu` using `Kum.cardSUnit F (S : Set (Pl F)) 2 hS`. Establish `hne : Nat.card (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸ (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) ≠ 0`. Rewrite using `[hc, hu]`.

Establish `h1 : Nat.card ↥(rootsOfUnity 2 F) ≠ 0` using `Nat.card_pos.ne'`. Establish `h2 : Nat.card { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } ≠ 0` using `by haveI : Nonempty { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } := ⟨⟨1, one_pow 2⟩⟩`. Conclude with `Nat.card_pos.ne'`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) h1) h2`. Use `haveI := Nat.finite_of_card_ne_zero hne`.

Set `f : {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2} → (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸ (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2))` to `fun c => QuotientGroup.mk ⟨c.1.out, c.2⟩`. Establish `hf : Function.Injective f`. Introduce and unpack `⟨c, hc⟩ ⟨c', hc'⟩ h`. Establish `h'` using `QuotientGroup.eq.mp h`. Rewrite `h'` using `[Subgroup.mem_subgroupOf]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Simplify `h'` using `[Kum.powK]`.

Conclude with `Set.finite_coe_iff.mp (Finite.of_injective f hf)`.
-/
private theorem fin_sel (S : Finset (Pl F)) :
    {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2}.Finite := by
  classical
  have hS : (S : Set (Pl F)).Finite := S.finite_toSet
  have hc := Kum.cardSel F (S : Set (Pl F)) 2 two_ne_zero
  have hu := Kum.cardSUnit F (S : Set (Pl F)) 2 hS
  have hne : Nat.card (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸
      (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) ≠ 0 := by
    rw [hc, hu]
    have h1 : Nat.card ↥(rootsOfUnity 2 F) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } ≠ 0 := by
      haveI : Nonempty { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } := ⟨⟨1, one_pow 2⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) h1) h2
  haveI := Nat.finite_of_card_ne_zero hne
  let f : {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2} →
      (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸ (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) :=
    fun c => QuotientGroup.mk ⟨c.1.out, c.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h' := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    apply Subtype.ext
    show c = c'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    apply QuotientGroup.eq.mpr
    simpa [Kum.powK] using h'
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

variable {Δ : F} (D : Dat Δ)

/- English proof (translation)
Establish `h` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))`. Take `⟨b, hb⟩` from `h`. Establish `hb' : b ^ 2 = (Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))⁻¹ * a` using `hb`. Use `⟨b⁻¹, ?_⟩` and prove the remaining obligations. Establish `e : Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = a * (b⁻¹) ^ 2`.

Rewrite using `[inv_pow, hb']`. Use `group`. Rewrite using `[e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem quotient_out_eq_mul_sq (a : Fˣ) :
    ∃ b : Fˣ, ((Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) : Fˣ) : F) = (a : F) * (b : F) ^ 2 := by
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))
  obtain ⟨b, hb⟩ := h
  have hb' : b ^ 2 = (Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))⁻¹ * a := hb
  refine ⟨b⁻¹, ?_⟩
  have e : Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = a * (b⁻¹) ^ 2 := by
    rw [inv_pow, hb']
    group
  rw [e]
  push_cast
  ring

/- English proof (translation)
Take `⟨b, hb⟩` from `quotient_out_eq_mul_sq a`. Simplify using `only [Dat.Sel, Set.mem_setOf_eq]`. Rewrite using `[hb]`. Prove the components needed by the constructor for the conclusion. Introduce `σ`.

Rewrite using `[map_mul, map_pow]`. Establish `hne : σ (b : F) ≠ 0` using `(map_ne_zero σ).mpr b.ne_zero`. Conclude with `mul_pos (h σ) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)`. Introduce `v hv`. Rewrite using `[show (a : F) * (b : F) ^ 2 * y = ((a : F) * y) * (b : F) ^ 2 by ring, map_mul, map_pow]`.

Conclude with `ev_mul (h' v hv) (ev_sq ((map_ne_zero _).mpr b.ne_zero))`.
-/
private theorem mem_sel (y : F) (a : Fˣ) (h : TPos (a : F)) (h' : D.Ev ((a : F) * y)) :
    (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
  obtain ⟨b, hb⟩ := quotient_out_eq_mul_sq a
  simp only [Dat.Sel, Set.mem_setOf_eq]
  rw [hb]
  constructor
  · intro σ
    rw [map_mul, map_pow]
    have hne : σ (b : F) ≠ 0 := (map_ne_zero σ).mpr b.ne_zero
    exact mul_pos (h σ) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)
  · intro v hv
    rw [show (a : F) * (b : F) ^ 2 * y = ((a : F) * y) * (b : F) ^ 2 by ring, map_mul, map_pow]
    exact ev_mul (h' v hv) (ev_sq ((map_ne_zero _).mpr b.ne_zero))

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym.Glob in
/- English proof (translation)
Introduce `F _ _ Δ D hOk`. Use `haveI := hOk.real`. Establish `hfin1 : (D.Sel 1).Finite`. Use `(fin_sel D.Sg).subset ?_` and prove the remaining obligations. Introduce `c hc v hv`.

Conclude with `dvd_of_ev v _ (by simpa using hc.2 v (by simpa using hv))`. Establish `hnon : (D.Sel 1).Nonempty` using `⟨_, mem_sel D 1 1 (fun σ => by simp) (fun v _ => by simpa using ev_sq (O := Ov v) (one_ne_zero (α := Kv v)))⟩`. Use `⟨hfin1, hnon, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `σ0` using `InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)`. Establish `hy0 : y ≠ 0` using `fun h0 => by`. Use `hy σ0` as an intermediate fact. Simplify using `[h0] at this`. Take `⟨yU, hyU⟩ : ∃ u : Fˣ, (u : F) = y` from `⟨Units.mk0 y hy0, rfl⟩`.

Establish `hmul : ∀ c ∈ D.Sel 1, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y`. Introduce `c hc`. Establish `e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Rewrite using `[e]`.

Apply `mem_sel D y` to reduce the goal to its premises. Introduce `σ`. Rewrite using `[Units.val_mul, hyU, map_mul]`. Conclude with `mul_pos (hc.1 σ) (hy σ)`. Introduce `v hv`.

Establish `h1` using `hc.2 v hv`. Rewrite using `[show ((c.out * yU : Fˣ) : F) * y = ((c.out : F) * 1) * y ^ 2 by rw [Units.val_mul, hyU]; ring, map_mul (cv v), map_pow]`. Conclude with `ev_mul h1 (ev_sq ((map_ne_zero _).mpr hy0))`. Establish `hback : ∀ c ∈ D.Sel y, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel 1`. Introduce `c hc`.

Establish `e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Rewrite using `[e]`. Apply `mem_sel D 1` to reduce the goal to its premises. Introduce `σ`.

Rewrite using `[Units.val_mul, hyU, map_mul]`. Conclude with `mul_pos (hc.1 σ) (hy σ)`. Introduce `v hv`. Rewrite using `[Units.val_mul, hyU, mul_one]`. Conclude with `hc.2 v hv`.

Establish `hsq : (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1`. Rewrite using `[← QuotientGroup.mk_mul]`. Conclude with `(QuotientGroup.eq_one_iff _).mpr ⟨yU, sq yU⟩`. Establish `himg : (fun c => c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) '' D.Sel 1 = D.Sel y`. Use extensionality with `c`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c', hc', rfl⟩`. Conclude with `hmul c' hc'`. Introduce `hc`. Use `⟨c * yU, hback c hc, ?_⟩` and prove the remaining obligations.

Use `show c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = c`. Rewrite using `[mul_assoc, hsq, mul_one]`. Establish `hinj : Function.Injective (fun c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range => c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))` using `mul_left_injective _`. Rewrite using `[← himg]`. Conclude with `⟨hfin1.image _, Set.ncard_image_of_injective _ hinj⟩`.
-/
theorem UpperTheory.V.Z.Sym.Glob.selCard :
    UpperTheory.V.Z.Sym.Glob.SelCard := by
  intro F _ _ Δ D hOk
  haveI := hOk.real
  have hfin1 : (D.Sel 1).Finite := by
    refine (fin_sel D.Sg).subset ?_
    intro c hc v hv
    exact dvd_of_ev v _ (by simpa using hc.2 v (by simpa using hv))
  have hnon : (D.Sel 1).Nonempty :=
    ⟨_, mem_sel D 1 1 (fun σ => by simp)
      (fun v _ => by simpa using ev_sq (O := Ov v) (one_ne_zero (α := Kv v)))⟩
  refine ⟨hfin1, hnon, ?_⟩
  intro y hy
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have σ0 := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy σ0
    simp [h0] at this
  obtain ⟨yU, hyU⟩ : ∃ u : Fˣ, (u : F) = y := ⟨Units.mk0 y hy0, rfl⟩
  have hmul : ∀ c ∈ D.Sel 1, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D y
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      have h1 := hc.2 v hv
      rw [show ((c.out * yU : Fˣ) : F) * y = ((c.out : F) * 1) * y ^ 2 by rw [Units.val_mul, hyU]; ring,
        map_mul (cv v), map_pow]
      exact ev_mul h1 (ev_sq ((map_ne_zero _).mpr hy0))
  have hback : ∀ c ∈ D.Sel y, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel 1 := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D 1
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      rw [Units.val_mul, hyU, mul_one]
      exact hc.2 v hv
  have hsq : (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨yU, sq yU⟩
  have himg : (fun c => c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) '' D.Sel 1 = D.Sel y := by
    ext c
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact hmul c' hc'
    · intro hc
      refine ⟨c * yU, hback c hc, ?_⟩
      show c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = c
      rw [mul_assoc, hsq, mul_one]
  have hinj : Function.Injective (fun c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range =>
      c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) := mul_left_injective _
  rw [← himg]
  exact ⟨hfin1.image _, Set.ncard_image_of_injective _ hinj⟩
