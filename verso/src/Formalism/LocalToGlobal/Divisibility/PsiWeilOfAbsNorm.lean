import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.Columns.StdLatUnimodular

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

section Txt

variable (D : Formalism.BasicNotions.D7)

instance gNeZero (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def xiBar (PP : Pl D.host.E) : kP PP := Formalism.L2.Col.redP PP D.host.xi0

def psiTxt {PP : Pl D.host.E} {n : ℕ} [NeZero n] (res : kP PP ≃+* ZMod n) : AddChar (kP PP) ℂ :=
  (ZMod.stdAddChar (N := n)).compAddMonoidHom
    (res.toRingHom.toAddMonoidHom.comp (AddMonoidHom.mulLeft (xiBar D PP)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiTxt_apply {PP : Pl D.host.E} {n : ℕ} [NeZero n] (res : kP PP ≃+* ZMod n) (c : kP PP) :
    psiTxt D res c = ZMod.stdAddChar (res (xiBar D PP * c)) := rfl

def PsiWeil (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) : Prop :=
  ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (c : kP (pl kv).1) (b : ℤ), xiBar D (pl kv).1 * c = (b : kP (pl kv).1) →
    D.what₂.embLL (ψ (pl kv).1 c) = Complex.exp (2 * Real.pi * Complex.I * b / (D.host.g kv.1 : ℂ))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h kv c`. Rewrite using `[psiTxt_apply]`. Use `set z := res kv (xiBar D (pl kv).1 * c) with hz`. Establish `hb : xiBar D (pl kv).1 * c = (((z.val : ℤ)) : kP (pl kv).1)`.

Apply `(res kv).injective` to reduce the goal to its premises. Rewrite using `[map_intCast, ← hz]`. Simplify using `[ZMod.natCast_zmod_val]`. Rewrite using `[h kv c _ hb, ZMod.stdAddChar_apply, ZMod.toCircle_apply]`. Use `push_cast`.

Put the polynomial expressions in normal form. Introduce `h kv c b hb`. Rewrite using `[h kv c, psiTxt_apply, hb, map_intCast, ZMod.stdAddChar_coe]`.
-/
theorem psiWeil_iff (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) :
    PsiWeil D Pg pl ψ ↔ ∀ kv (c : kP (pl kv).1), D.what₂.embLL (ψ (pl kv).1 c) = psiTxt D (res kv) c := by
  constructor
  · intro h kv c
    rw [psiTxt_apply]
    set z := res kv (xiBar D (pl kv).1 * c) with hz
    have hb : xiBar D (pl kv).1 * c = (((z.val : ℤ)) : kP (pl kv).1) := by
      apply (res kv).injective
      rw [map_intCast, ← hz]
      simp [ZMod.natCast_zmod_val]
    rw [h kv c _ hb, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast
    ring_nf
  · intro h kv c b hb
    rw [h kv c, psiTxt_apply, hb, map_intCast, ZMod.stdAddChar_coe]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr r.toEquiv, Nat.card_zmod]`.
-/
theorem absNorm_eq_of_res {PP : Pl D.host.E} {n : ℕ} (r : kP PP ≃+* ZMod n) [NeZero n] : Ideal.absNorm PP.asIdeal = n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr r.toEquiv, Nat.card_zmod]

/- English proof (translation)
Introduce `kv c b hb`. Rewrite using `[h kv c b hb, absNorm_eq_of_res D (res kv)]`.
-/
theorem psiWeil_of_absNorm {Pg : Finset (Pl D.host.E)} (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL}
    (h : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (c : kP (pl kv).1) (b : ℤ), xiBar D (pl kv).1 * c = (b : kP (pl kv).1) →
      D.what₂.embLL (ψ (pl kv).1 c) =
        Complex.exp (2 * Real.pi * Complex.I * b / ((Ideal.absNorm (pl kv).1.asIdeal : ℕ) : ℂ))) :
    PsiWeil D Pg pl ψ := by
  intro kv c b hb
  rw [h kv c b hb, absNorm_eq_of_res D (res kv)]

/- English proof (translation)
Introduce `hψ`. Establish `h1` using `h kv c 1 (by rw [Int.cast_one]; exact hc)`. Rewrite `h1` using `[hψ, AddChar.one_apply, map_one]`. Establish `hg` using `D.host.g_prime kv.1`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.mp h1.symm`.

Establish `hgC : (D.host.g kv.1 : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hg.ne_zero`. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Rewrite `hm` using `[Int.cast_one, mul_one, div_eq_iff hgC]`. Establish `h3 : (2 * Real.pi * Complex.I : ℂ) * (1 - m * D.host.g kv.1) = 0`.

Take the linear combination `hm`. Establish `h4 : (1 : ℂ) - m * D.host.g kv.1 = 0` using `(mul_eq_zero.mp h3).resolve_left hpi`. Establish `h5 : (1 : ℤ) = m * D.host.g kv.1`. Establish `: (1 : ℂ) = m * D.host.g kv.1` using `by linear_combination h4`. Conclude with `this` after adjusting the coercions.

Establish `h6 : (D.host.g kv.1 : ℤ) ∣ 1` using `⟨m, by rw [h5]; ring⟩`. Establish `h7 : D.host.g kv.1 ∣ 1` using `by exact_mod_cast h6`. Conclude with `hg.one_lt.ne' (Nat.dvd_one.mp h7)`.
-/
theorem PsiWeil.ne_one {Pg : Finset (Pl D.host.E)} {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} (h : PsiWeil D Pg pl ψ) (kv : Σ k : Fin 2, D.nd.PlG k)
    (c : kP (pl kv).1) (hc : xiBar D (pl kv).1 * c = 1) : ψ (pl kv).1 ≠ 1 := by
  intro hψ
  have h1 := h kv c 1 (by rw [Int.cast_one]; exact hc)
  rw [hψ, AddChar.one_apply, map_one] at h1
  have hg := D.host.g_prime kv.1
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1.symm
  have hgC : (D.host.g kv.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne_zero
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [Int.cast_one, mul_one, div_eq_iff hgC] at hm
  have h3 : (2 * Real.pi * Complex.I : ℂ) * (1 - m * D.host.g kv.1) = 0 := by
    linear_combination hm
  have h4 : (1 : ℂ) - m * D.host.g kv.1 = 0 := (mul_eq_zero.mp h3).resolve_left hpi
  have h5 : (1 : ℤ) = m * D.host.g kv.1 := by
    have : (1 : ℂ) = m * D.host.g kv.1 := by linear_combination h4
    exact_mod_cast this
  have h6 : (D.host.g kv.1 : ℤ) ∣ 1 := ⟨m, by rw [h5]; ring⟩
  have h7 : D.host.g kv.1 ∣ 1 := by exact_mod_cast h6
  exact hg.one_lt.ne' (Nat.dvd_one.mp h7)

/- English proof (translation)
Use `⟨(AddChar.zmodChar n hζ).compAddMonoidHom (res.toRingHom.toAddMonoidHom.comp (AddMonoidHom.mulLeft (xiBar D PP))), fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[psiTxt_apply, AddChar.compAddMonoidHom_apply]`. Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AddChar.zmodChar_apply, map_pow, he]`. Rewrite using `[ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_nat_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_psiTxt_lift {PP : Pl D.host.E} {n : ℕ} [NeZero n] (res : kP PP ≃+* ZMod n) {ζ : D.what₂.LL} (hζ : ζ ^ n = 1)
    (he : D.what₂.embLL ζ = Complex.exp (2 * Real.pi * Complex.I / n)) :
    ∃ χ : AddChar (kP PP) D.what₂.LL, ∀ c, D.what₂.embLL (χ c) = psiTxt D res c := by
  refine ⟨(AddChar.zmodChar n hζ).compAddMonoidHom
    (res.toRingHom.toAddMonoidHom.comp (AddMonoidHom.mulLeft (xiBar D PP))), fun c => ?_⟩
  rw [psiTxt_apply, AddChar.compAddMonoidHom_apply]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AddChar.zmodChar_apply, map_pow, he]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_nat_mul]
  congr 1
  ring

def psiAt {Pg : Finset (Pl D.host.E)} (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)) (ζ : Fin 2 → D.what₂.LL)
    (hζ : ∀ k, ζ k ^ D.host.g k = 1) (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pl D.host.E) (e : (pl kv).1 = PP) :
    AddChar (kP PP) D.what₂.LL := by
  subst e
  exact (AddChar.zmodChar (D.host.g kv.1) (hζ kv.1)).compAddMonoidHom
    ((res kv).toRingHom.toAddMonoidHom.comp (AddMonoidHom.mulLeft (xiBar D (pl kv).1)))

/- English proof (translation)
Substitute `e` using the available equality. Establish `hv : psiAt D pl res ζ hζ kv (pl kv).1 rfl c = ζ kv.1 ^ (res kv (xiBar D (pl kv).1 * c)).val`. Simplify using `[psiAt, AddChar.zmodChar_apply]`. Rewrite using `[hv, map_pow, he, hb, map_intCast, ← Complex.exp_nat_mul]`. Establish `h2` using `ZMod.toCircle_intCast (N := D.host.g kv.1) b`.

Rewrite `h2` using `[ZMod.toCircle_apply]`. Rewrite using `[← h2]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiAt_spec {Pg : Finset (Pl D.host.E)} (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)) {ζ : Fin 2 → D.what₂.LL}
    (hζ : ∀ k, ζ k ^ D.host.g k = 1)
    (he : ∀ k, D.what₂.embLL (ζ k) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ)))
    (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pl D.host.E) (e : (pl kv).1 = PP) (c : kP PP) (b : ℤ)
    (hb : xiBar D PP * c = (b : kP PP)) :
    D.what₂.embLL (psiAt D pl res ζ hζ kv PP e c) = Complex.exp (2 * Real.pi * Complex.I * b / (D.host.g kv.1 : ℂ)) := by
  subst e
  have hv : psiAt D pl res ζ hζ kv (pl kv).1 rfl c =
      ζ kv.1 ^ (res kv (xiBar D (pl kv).1 * c)).val := by
    simp [psiAt, AddChar.zmodChar_apply]
  rw [hv, map_pow, he, hb, map_intCast, ← Complex.exp_nat_mul]
  have h2 := ZMod.toCircle_intCast (N := D.host.g kv.1) b
  rw [ZMod.toCircle_apply] at h2
  rw [← h2]
  congr 1
  ring

open Classical in

def psiOfRoots {Pg : Finset (Pl D.host.E)} (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)) (ζ : Fin 2 → D.what₂.LL)
    (hζ : ∀ k, ζ k ^ D.host.g k = 1) (PP : Pl D.host.E) : AddChar (kP PP) D.what₂.LL :=
  if h : PP ∈ Pg then psiAt D pl res ζ hζ (pl.symm ⟨PP, h⟩) PP (by simp) else 1

/- English proof (translation)
Introduce `kv c b hb`. Establish `hmem : (pl kv).1 ∈ Pg` using `(pl kv).2`. Establish `hkv : pl.symm ⟨(pl kv).1, hmem⟩ = kv` using `by simp`. Establish `hspec` using `psiAt_spec D pl res hζ he (pl.symm ⟨(pl kv).1, hmem⟩) (pl kv).1 (by simp) c b hb`. Unfold `psiOfRoots`.

Rewrite using `[dif_pos hmem, hspec, hkv]`.
-/
theorem exists_psiWeil {Pg : Finset (Pl D.host.E)} (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)) {ζ : Fin 2 → D.what₂.LL}
    (hζ : ∀ k, ζ k ^ D.host.g k = 1)
    (he : ∀ k, D.what₂.embLL (ζ k) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) :
    PsiWeil D Pg pl (psiOfRoots D pl res ζ hζ) := by
  intro kv c b hb
  have hmem : (pl kv).1 ∈ Pg := (pl kv).2
  have hkv : pl.symm ⟨(pl kv).1, hmem⟩ = kv := by simp
  have hspec := psiAt_spec D pl res hζ he (pl.symm ⟨(pl kv).1, hmem⟩) (pl kv).1 (by simp) c b hb
  unfold psiOfRoots
  rw [dif_pos hmem, hspec, hkv]

def XiOneClass : Prop :=
  ∀ k : Fin 2, ∃ b : ℤ, ¬ (D.host.g k : ℤ) ∣ b ∧ ∀ v : D.nd.PlG k, xiBar D (D.naut.plGw k v) = (b : kP (D.naut.plGw k v))

end Txt

section Det

variable {D : Formalism.BasicNotions.D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* Formalism.BasicNotions.G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}

variable (D) in
open Classical in

def pgOf : Finset (Pl D.host.E) := Finset.univ.image fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.naut.plGw kv.1 kv.2

/- English proof (translation)
Use extensionality with `PP`. Simplify using `only [pgOf, Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `hP`. Conclude with `⟨pl.symm ⟨PP, hP⟩, by rw [← h.place]; simp⟩`.

Introduce and unpack `⟨kv, rfl⟩`. Rewrite using `[← h.place]`. Conclude with `(pl kv).2`.
-/
theorem LvlTie.pg_eq (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) : Pg = pgOf D := by
  ext PP
  simp only [pgOf, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hP
    exact ⟨pl.symm ⟨PP, hP⟩, by rw [← h.place]; simp⟩
  · rintro ⟨kv, rfl⟩
    rw [← h.place]
    exact (pl kv).2

/- English proof (translation)
The claim follows from `Equiv.ext fun kv => Subtype.ext (by rw [h.place, h'.place])`.
-/
theorem LvlTie.pl_unique {pl' : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg}
    {res' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl' kv).1 ≃+* ZMod (D.host.g kv.1)}
    {ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC' : G ≃* G0 Pg D.R.r}
    (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (h' : LvlTie D P0 ψ0 Ps ψs eG Pg pl' res' ψ' eC') : pl = pl' :=
  Equiv.ext fun kv => Subtype.ext (by rw [h.place, h'.place])

/- English proof (translation)
Establish `hs : r.symm = r'.symm` using `RingEquiv.toRingHom_injective (Subsingleton.elim _ _)`. Rewrite using `[← r.symm_symm, hs, RingEquiv.symm_symm]`.
-/
theorem res_unique {R : Type} [Semiring R] {n : ℕ} (r r' : R ≃+* ZMod n) : r = r' := by
  have hs : r.symm = r'.symm := RingEquiv.toRingHom_injective (Subsingleton.elim _ _)
  rw [← r.symm_symm, hs, RingEquiv.symm_symm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[h.comp g kv, Matrix.GeneralLinearGroup.map_apply]`.
-/
theorem LvlTie.eC_eq (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : G) (kv : Σ k : Fin 2, D.nd.PlG k) :
    eC g (pl kv) = Matrix.GeneralLinearGroup.map (res kv).symm.toRingHom (eG g kv) := by
  ext i j
  simp [h.comp g kv, Matrix.GeneralLinearGroup.map_apply]

/- English proof (translation)
Use `MulEquiv.ext fun g => funext fun PP => ?_` and prove the remaining obligations. Take `⟨kv, rfl⟩` from `pl.surjective PP`. Rewrite using `[LvlTie.eC_eq h g kv, LvlTie.eC_eq h' g kv, res_unique (res kv) (res' kv)]`.
-/
theorem LvlTie.eC_unique {res' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
    {ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC' : G ≃* G0 Pg D.R.r}
    (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (h' : LvlTie D P0 ψ0 Ps ψs eG Pg pl res' ψ' eC') : eC = eC' := by
  refine MulEquiv.ext fun g => funext fun PP => ?_
  obtain ⟨kv, rfl⟩ := pl.surjective PP
  rw [LvlTie.eC_eq h g kv, LvlTie.eC_eq h' g kv, res_unique (res kv) (res' kv)]

end Det

section Comparison₂

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G]

def PsiPPTie (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (eG : G ≃* Formalism.BasicNotions.G0g D.nd) : Prop :=
  ∃ (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
    (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) (eC : G ≃* G0 Pg D.R.r),
    LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC ∧ PsiWeil D Pg pl ψ

variable {D}

/- English proof (translation)
Take `⟨Pg, pl, res, ψ, eC, h1, -⟩` from `h`. Conclude with `⟨Pg, pl, res, ψ, eC, h1⟩`.
-/
theorem PsiPPTie.lvl {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* Formalism.BasicNotions.G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) :
    ∃ (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
      (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
      (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) (eC : G ≃* G0 Pg D.R.r),
      LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC := by
  obtain ⟨Pg, pl, res, ψ, eC, h1, -⟩ := h
  exact ⟨Pg, pl, res, ψ, eC, h1⟩

/- English proof (translation)
Take `⟨Pg, pl, res, ψ, eC, h1, h2⟩` from `h`. Conclude with `⟨Pg, pl, res, ψ, eC, h1, h1.pg_eq, h1.place, (psiWeil_iff D Pg pl res ψ).mp h2, fun g kv => h1.eC_eq g kv⟩`.
-/
theorem PsiPPTie.spec {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* Formalism.BasicNotions.G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) :
    ∃ (Pg : Finset (Pl D.host.E)) (pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg)
      (res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1))
      (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL) (eC : G ≃* G0 Pg D.R.r),
      LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC ∧ Pg = pgOf D ∧
      (∀ kv, ((pl kv : Pl D.host.E)) = D.naut.plGw kv.1 kv.2) ∧
      (∀ kv (c : kP (pl kv).1), D.what₂.embLL (ψ (pl kv).1 c) = psiTxt D (res kv) c) ∧
      ∀ g kv, eC g (pl kv) = Matrix.GeneralLinearGroup.map (res kv).symm.toRingHom (eG g kv) := by
  obtain ⟨Pg, pl, res, ψ, eC, h1, h2⟩ := h
  exact ⟨Pg, pl, res, ψ, eC, h1, h1.pg_eq, h1.place, (psiWeil_iff D Pg pl res ψ).mp h2,
    fun g kv => h1.eC_eq g kv⟩

end Comparison₂

section Forms

open Formalism.DivisionValues Formalism.L2.Indef

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)

abbrev PsiPPTie2 (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A.side Ps ψs Zs)} (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop :=
  PsiPPTie D P0 ψ0 Ps ψs I.eG

variable {Pl0 I0 Ty : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m)

abbrev PsiPPTie3 (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A3.side3 Ps ψs Zs)} (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop :=
  PsiPPTie D P0 ψ0 Ps ψs I.eG

end Forms

end Formalism.L2.DIV
